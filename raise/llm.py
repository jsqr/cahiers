"""LLM functions for structured output using Instructor and Pydantic."""

import os

import instructor
from mistralai import Mistral
from pydantic import BaseModel


class Verification(BaseModel):
    """Result of verifying a property against text."""

    satisfied: bool
    confidence: float
    reasoning: str


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
    return [verify_property(client, text, prop) for prop in properties]
