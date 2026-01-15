"""
Utilities for parsing and processing NY State legislative bill text files,
specifically the RAISE Act (Responsible AI Safety and Education Act).
"""

import re
from pathlib import Path


def identify_article_start(text: str) -> int | None:
    """
    Identify the start of the substantive part of the bill by matching 'ARTICLE'.

    Returns the character index of the start of the ARTICLE line, or None if not found.
    """
    match = re.search(r"^\s*ARTICLE\s+\d+", text, re.MULTILINE)
    if match:
        return match.start()
    # Also try matching "ARTICLE 44-B" style
    match = re.search(r"^\s*ARTICLE\s+[\d\w-]+", text, re.MULTILINE)
    if match:
        return match.start()
    return None


def identify_page_breaks(text: str) -> list[tuple[int, int, str]]:
    """
    Identify page breaks in the text.

    Page breaks appear as:
    - A centered header line (e.g., "A. 6453                             2")
    - Possibly preceded/followed by blank lines

    Returns a list of tuples: (start_index, end_index, header_text)
    """
    # Pattern matches lines like "A. 6453                             2" or "S. 6953--B                          3"
    # These have a bill identifier, lots of whitespace, and a page number
    pattern = r"\n\s*([AS]\.\s*\d+(?:--[A-Z])?\s{10,}\d+)\s*\n"

    matches = []
    for match in re.finditer(pattern, text):
        matches.append((match.start(), match.end(), match.group(1).strip()))

    return matches


def remove_page_breaks(text: str) -> str:
    """
    Remove page break headers from the text.
    """
    # Pattern for page break lines
    pattern = r"\n\s*[AS]\.\s*\d+(?:--[A-Z])?\s{10,}\d+\s*\n"
    return re.sub(pattern, "\n", text)


def remove_explanation_lines(text: str) -> str:
    """
    Remove the EXPLANATION footer lines that appear at the bottom of pages.
    These look like:
      EXPLANATION--Matter in ITALICS (underscored) is new; matter in brackets
                         [ ] is old law to be omitted.
                                                              LBD00047-07-5
    """
    # Remove EXPLANATION lines and the following lines that are part of it
    pattern = r"\s*EXPLANATION--Matter in ITALICS.*?LBD\d+-\d+-\d+\s*"
    text = re.sub(pattern, " ", text, flags=re.DOTALL)
    return text


def rejoin_hyphenated_words(text: str) -> str:
    """
    Rejoin words that were split with hyphens at line breaks.
    E.g., "RECOMMEN-\nDATIONS" -> "RECOMMENDATIONS"
    Also handles cases where newlines have already been converted to spaces:
    E.g., "RECOMMEN- DATIONS" -> "RECOMMENDATIONS"

    Excludes cases where the hyphen is part of a compound construction like
    "MACHINE- AND HUMAN-BASED" (hyphen before AND/OR).
    """

    # Pattern: hyphen at end of line followed by continuation (with newline)
    # Exclude cases where continuation is AND/OR (compound constructions)
    def rejoin_newline(match):
        first, second = match.group(1), match.group(2)
        # Don't rejoin if second word is AND/OR (compound like "MACHINE- AND")
        if second.upper() in ("AND", "OR"):
            return f"{first}- {second}"
        return first + second

    pattern = r"(\w+)-\s*\n\s*(\w+)"
    text = re.sub(pattern, rejoin_newline, text)

    # Pattern: hyphen followed by space and continuation (after newlines became spaces)
    # Only rejoin if both parts are uppercase (typical of split legislative text)
    # and second part is not AND/OR
    def rejoin_if_split(match):
        first, second = match.group(1), match.group(2)
        # Don't rejoin if second word is AND/OR (compound like "MACHINE- AND")
        if second.upper() in ("AND", "OR"):
            return match.group(0)
        # If both parts are uppercase, likely a split word
        if first.isupper() and second.isupper():
            return first + second
        # Keep the original (legitimate hyphenated term)
        return match.group(0)

    pattern = r"(\b[A-Z]+)- ([A-Z]+\b)"
    text = re.sub(pattern, rejoin_if_split, text)
    return text


def regularize_text(text: str) -> str:
    """
    Regularize a block of text by:
    - Rejoining hyphenated words split across lines
    - Removing extra spaces between words
    - Removing extra whitespace before and after
    - Removing internal newlines (joining wrapped lines)
    """
    # First rejoin hyphenated words
    text = rejoin_hyphenated_words(text)
    # Replace newlines with spaces
    text = text.replace("\n", " ")
    # Collapse multiple spaces into one
    text = re.sub(r" +", " ", text)
    # Strip leading/trailing whitespace
    return text.strip()


def is_toc_entry(line: str) -> bool:
    """
    Check if a line is a table of contents entry.
    TOC entries are numbered items that reference section numbers (4-digit numbers).
    E.g., "1421. TRANSPARENCY REQUIREMENTS..."
    """
    # TOC entries have 4-digit section numbers
    return bool(re.match(r"^\s*\d{4}\.\s+", line))


def parse_section_hierarchy(text: str) -> list[dict]:
    """
    Parse the bill text into a hierarchical structure of sections.

    Hierarchy levels:
    1. ARTICLE - e.g., "ARTICLE 44-B"
    2. SECTION - e.g., "§ 1420." or "SECTION 1420."
    3. Numbered paragraph - e.g., "1.", "2.", "12."
    4. Lettered paragraph - e.g., "(A)", "(B)"
    5. Roman numeral subparagraph - e.g., "(I)", "(II)", "(III)"

    Returns a list of dicts with keys: level, designator, text, raw
    """
    sections = []

    # First, remove explanation lines
    text = remove_explanation_lines(text)

    # Patterns for different hierarchy levels
    patterns = [
        # Level 1: ARTICLE (standalone line or with title on next line)
        (1, r"^(\s*ARTICLE\s+[\d\w-]+)\s*$", "article"),
        # Level 2: Section header in table of contents (e.g., "SECTION 1420. DEFINITIONS.")
        (2, r"^\s*(SECTION\s+\d+)\.\s+(.+?)\s*$", "section_toc"),
        # Level 2: Section (e.g., "§ 1420." or "§ 1420. DEFINITIONS.")
        (2, r"^\s*(§\s*\d+)\.\s*(.*)$", "section"),
        # Level 3: Numbered paragraph at start of line (e.g., "1.", "12.")
        # but NOT 4-digit section numbers (those are TOC entries)
        (3, r"^\s*(\d{1,2})\.\s+(.*)$", "numbered"),
        # Level 4: Lettered paragraph (e.g., "(A)", "(B)")
        (4, r"^\s*\(([A-Z])\)\s+(.*)$", "lettered"),
        # Level 5: Roman numeral subparagraph (e.g., "(I)", "(II)")
        (5, r"^\s*\(([IVX]+)\)\s+(.*)$", "roman"),
    ]

    lines = text.split("\n")
    current_section = None
    in_toc = False  # Track if we're in the table of contents

    for i, line in enumerate(lines):
        # Skip empty lines
        if not line.strip():
            continue

        # Check if this is a TOC entry (4-digit section number)
        if is_toc_entry(line):
            in_toc = True
            # Skip TOC entries - they'll be captured when we hit the actual sections
            continue

        matched = False

        for level, pattern, kind in patterns:
            match = re.match(pattern, line, re.IGNORECASE if kind == "article" else 0)
            if match:
                # For numbered patterns, skip if it looks like a TOC entry
                if kind == "numbered":
                    # If the number is 4 digits, it's a section reference in TOC
                    num = match.group(1)
                    if len(num) == 4:
                        continue

                # When we hit a real section (§), we're out of TOC
                if kind == "section":
                    in_toc = False

                # Save previous section if exists
                if current_section:
                    sections.append(current_section)

                if kind == "article":
                    designator = match.group(1).strip()
                    section_text = ""
                    # Check if next line has the article title
                    if i + 1 < len(lines):
                        next_line = lines[i + 1].strip()
                        # Article titles are typically in all caps and centered
                        if (
                            next_line
                            and next_line.isupper()
                            and not next_line.startswith("SECTION")
                        ):
                            section_text = next_line
                elif kind == "section_toc":
                    designator = match.group(1).strip()
                    section_text = match.group(2).strip()
                elif kind == "section":
                    designator = match.group(1).strip()
                    section_text = match.group(2).strip() if match.group(2) else ""
                else:
                    designator = match.group(1)
                    section_text = (
                        match.group(2).strip() if len(match.groups()) > 1 else ""
                    )

                current_section = {
                    "level": level,
                    "kind": kind,
                    "designator": designator,
                    "text": section_text,
                    "raw": line,
                }
                matched = True
                break

        # If no pattern matched and we have a current section (and not in TOC), append to its text
        if not matched and current_section and line.strip() and not in_toc:
            # Skip the article title line if we already captured it
            if (
                current_section["kind"] == "article"
                and current_section["text"] == line.strip()
            ):
                continue
            current_section["text"] += " " + line.strip()

    # Don't forget the last section
    if current_section:
        sections.append(current_section)

    # Regularize all text fields
    for section in sections:
        section["text"] = regularize_text(section["text"])

    return sections


def get_preamble(text: str) -> str:
    """
    Extract the preamble (everything before ARTICLE).
    """
    start = identify_article_start(text)
    if start is None:
        return ""
    return text[:start]


def get_body(text: str) -> str:
    """
    Extract the body (starting from ARTICLE).
    """
    start = identify_article_start(text)
    if start is None:
        return text
    return text[start:]


def sections_to_markdown(sections: list[dict]) -> str:
    """
    Convert parsed sections to Markdown format.

    Header levels:
    - Level 1 (ARTICLE): ##
    - Level 2 (SECTION): ###
    - Level 3 (numbered): ####
    - Level 4 (lettered): #####
    - Level 5 (roman): ######

    The heading contains only the designator (and title for articles/sections).
    Body text is placed in a separate paragraph below the heading.
    """
    md_lines = []

    level_to_hashes = {1: "##", 2: "###", 3: "####", 4: "#####", 5: "######"}

    for section in sections:
        level = section["level"]
        hashes = level_to_hashes.get(level, "######")
        designator = section["designator"]
        text = section["text"]

        # Format the heading (designator only, or designator + title for articles/sections)
        # Body text goes in a separate paragraph
        if section["kind"] == "article":
            # ARTICLE 44-B with optional title
            heading = f"{hashes} {designator}"
            body = text  # Article title becomes the body (or empty)
        elif section["kind"] in ("section", "section_toc"):
            # § 1420. DEFINITIONS. - the title is part of the heading for sections
            # But body text (if any beyond the title) is separate
            # For section_toc, text is just the title, no body
            # For section, we need to split title from body
            heading = f"{hashes} {designator}."
            body = text  # The definition text becomes body
        elif section["kind"] == "numbered":
            # 1. -> #### 1.
            heading = f"{hashes} {designator}."
            body = text
        elif section["kind"] == "lettered":
            # (A) -> ##### (A)
            heading = f"{hashes} ({designator})"
            body = text
        elif section["kind"] == "roman":
            # (I) -> ###### (I)
            heading = f"{hashes} ({designator})"
            body = text
        else:
            heading = f"{hashes} {designator}"
            body = text

        md_lines.append(heading)
        if body:
            md_lines.append("")  # Blank line between heading and body
            md_lines.append(body)
        md_lines.append("")  # Blank line after section

    return "\n".join(md_lines)


def process_bill_file(
    input_path: str | Path, output_path: str | Path | None = None
) -> str:
    """
    Process an entire bill file and convert to Markdown.

    Steps:
    1. Remove the preamble (before 'ARTICLE') and any page break lines
    2. Split the file into sections, subsections, and paragraphs
    3. Separate out the section text and number/letter designators
    4. Convert to Markdown with appropriate header levels
    5. Save to file with .md extension (if output_path not specified,
       replaces .txt with .md)

    Returns the Markdown string.
    """
    input_path = Path(input_path)

    # Read input file
    text = input_path.read_text(encoding="utf-8")

    # Remove page breaks
    text = remove_page_breaks(text)

    # Get body (from ARTICLE onwards)
    body = get_body(text)

    # Parse into sections
    sections = parse_section_hierarchy(body)

    # Convert to Markdown
    markdown = sections_to_markdown(sections)

    # Determine output path
    if output_path is None:
        output_path = input_path.with_suffix(".md")
    else:
        output_path = Path(output_path)

    # Write output file
    output_path.write_text(markdown, encoding="utf-8")

    return markdown


def process_all_bills(
    data_dir: str | Path, output_dir: str | Path | None = None
) -> dict[str, str]:
    """
    Process all bill text files in a directory.

    Returns a dict mapping input filenames to their Markdown output.
    """
    data_dir = Path(data_dir)
    if output_dir is None:
        output_dir = data_dir
    else:
        output_dir = Path(output_dir)

    results = {}

    for txt_file in data_dir.glob("*.txt"):
        output_path = output_dir / txt_file.with_suffix(".md").name
        try:
            md = process_bill_file(txt_file, output_path)
            results[txt_file.name] = md
        except Exception as e:
            print(f"Error processing {txt_file.name}: {e}")
            results[txt_file.name] = f"ERROR: {e}"

    return results


if __name__ == "__main__":
    # Example usage
    import sys

    if len(sys.argv) > 1:
        input_file = sys.argv[1]
        md = process_bill_file(input_file)
        print(f"Processed {input_file}")
        print(md[:500] + "..." if len(md) > 500 else md)
    else:
        # Process all files in ../data/
        data_dir = Path(__file__).parent.parent / "data"
        if data_dir.exists():
            results = process_all_bills(data_dir)
            for name, content in results.items():
                status = "OK" if not content.startswith("ERROR") else content
                print(f"{name}: {status[:50]}...")
