"""LLM functions for structured output using Instructor and Pydantic."""

import os
import time

import instructor
from mistralai import Mistral
from pydantic import BaseModel


class Verification(BaseModel):
    """Result of verifying a property against text."""

    satisfied: bool
    confidence: float
    reasoning: str


class Modification(BaseModel):
    """Result of modifying text to satisfy properties."""

    modified_text: str
    explanation: str


SYSTEM_PROMPT = """
You are a lawyer skilled at interpreting and drafting statutes. Given the text of a
statutory provision and a property, determine if the property is true. Provide your
confidence level (0.0 to 1.0) and a concise (1-2 sentence) statement about your reasoning.
""".strip()

USER_PROMPT_TEMPLATE = """
Text:
{text}

Property:
{property}

Does the text satisfy this property?
""".strip()

MODIFY_SYSTEM_PROMPT = """
You are a lawyer skilled at interpreting and drafting statutes. Your task is to modify
the given statutory text so that it satisfies the specified properties. Make minimal
changes necessary to satisfy the properties while preserving the overall structure and
intent of the statute. Preserve newlines and Markdown artifacts (like '#' symbols)
where possible. Return the complete modified text.
""".strip()

MODIFY_USER_PROMPT_TEMPLATE = """
Text to modify:
{text}

Properties that must be satisfied:
{properties}

Please modify the text so that all properties are satisfied.
""".strip()

MODIFY_WITH_FEEDBACK_TEMPLATE = """
Text to modify:
{text}

Properties that must be satisfied:
{properties}

Previous attempt failed verification. Here are the issues:
{feedback}

Please modify the text to address these issues and satisfy all properties.
""".strip()


def create_client():
    """Create and return an instructor-wrapped Mistral client.

    Returns:
        An instructor client for Mistral.

    Raises:
        ValueError: If MISTRAL_API_KEY is not set.
    """
    api_key = os.environ.get("MISTRAL_API_KEY")
    if not api_key:
        raise ValueError("MISTRAL_API_KEY environment variable not set")
    return instructor.from_mistral(Mistral(api_key=api_key))


def verify_property(client, text: str, property: str) -> Verification:
    """Verify a single property against the given text.

    Args:
        client: The instructor-wrapped Mistral client.
        text: The text to verify against.
        property: The property to check.

    Returns:
        A Verification result with satisfied status, confidence, and reasoning.
    """
    user_prompt = USER_PROMPT_TEMPLATE.format(text=text, property=property)

    result = client.chat.completions.create(
        model="mistral-large-2512",
        response_model=Verification,
        messages=[
            {"role": "system", "content": SYSTEM_PROMPT},
            {"role": "user", "content": user_prompt},
        ],
    )

    if result.confidence < 0.7:
        print(
            f"Warning: Low confidence ({result.confidence:.2f}) for property: {property}"
        )

    return result


def verify_properties(client, text: str, properties: list[str]) -> list[Verification]:
    """Verify multiple properties against the given text.

    Args:
        client: The instructor-wrapped Mistral client.
        text: The text to verify against.
        properties: List of properties to check.

    Returns:
        List of Verification results, one for each property.
    """
    results = []
    for i, prop in enumerate(properties):
        result = verify_property(client, text, prop)
        results.append(result)
        # Add a small delay between calls to avoid batching issues
        if i < len(properties) - 1:
            time.sleep(0.5)
    return results


def modify(
    client,
    text: str,
    properties: list[str],
    feedback: str | None = None,
    one_by_one: bool = False,
) -> Modification:
    """Modify text to satisfy the given properties.

    Args:
        client: The instructor-wrapped Mistral client.
        text: The text to modify.
        properties: List of properties the text should satisfy.
        feedback: Optional feedback from failed verification to guide modifications.
        one_by_one: If True, apply properties one at a time instead of all at once.

    Returns:
        A Modification result with modified text and explanation.
    """
    if one_by_one:
        # Apply properties one at a time
        current_text = text
        explanations = []
        for prop in properties:
            result = _modify_single(client, current_text, [prop], feedback=None)
            current_text = result.modified_text
            explanations.append(result.explanation)
            time.sleep(0.5)
        return Modification(
            modified_text=current_text,
            explanation=" | ".join(explanations),
        )
    else:
        return _modify_single(client, text, properties, feedback)


def _modify_single(
    client,
    text: str,
    properties: list[str],
    feedback: str | None = None,
) -> Modification:
    """Internal function to modify text for a set of properties."""
    properties_str = "\n".join(f"- {p}" for p in properties)

    if feedback:
        user_prompt = MODIFY_WITH_FEEDBACK_TEMPLATE.format(
            text=text,
            properties=properties_str,
            feedback=feedback,
        )
    else:
        user_prompt = MODIFY_USER_PROMPT_TEMPLATE.format(
            text=text,
            properties=properties_str,
        )

    result = client.chat.completions.create(
        model="mistral-large-2512",
        response_model=Modification,
        messages=[
            {"role": "system", "content": MODIFY_SYSTEM_PROMPT},
            {"role": "user", "content": user_prompt},
        ],
    )

    return result


def modify_to_satisfy(
    client,
    text: str,
    properties: list[str],
    max_iterations: int = 3,
    one_by_one: bool = False,
) -> tuple[str, list[Verification], bool, int]:
    """Iteratively modify text until all properties are satisfied.

    Args:
        client: The instructor-wrapped Mistral client.
        text: The text to modify.
        properties: List of properties the text should satisfy.
        max_iterations: Maximum number of modification attempts.
        one_by_one: If True, apply properties one at a time.

    Returns:
        Tuple of (final_text, final_verifications, success, iterations_used).
    """
    current_text = text
    feedback = None
    verifications = []

    for iteration in range(max_iterations):
        # Modify the text
        modification = modify(
            client, current_text, properties, feedback=feedback, one_by_one=one_by_one
        )
        current_text = modification.modified_text

        # Verify the modified text
        verifications = verify_properties(client, current_text, properties)

        # Check if all properties are satisfied
        all_satisfied = all(v.satisfied for v in verifications)
        if all_satisfied:
            return current_text, verifications, True, iteration + 1

        # Build feedback from failed verifications
        failed_feedback = []
        for prop, v in zip(properties, verifications):
            if not v.satisfied:
                failed_feedback.append(f"Property: {prop}\nReason: {v.reasoning}")
        feedback = "\n\n".join(failed_feedback)

    # Return final state after max iterations
    return current_text, verifications, False, max_iterations
