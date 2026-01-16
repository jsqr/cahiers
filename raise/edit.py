import marimo

__generated_with = "0.19.2"
app = marimo.App(width="medium")


@app.cell
def _():
    from pathlib import Path

    import marimo as mo
    from redlines import Redlines

    import llm
    import raise_md
    return Path, Redlines, llm, mo, raise_md


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # Verify properties of a statute and if necessary propose changes

    Getting started:

    1. Select a data directory containing raw `.txt` bill files
    2. Click "Preprocess" to convert them to markdown
    3. Select a preprocessed file to work with
    4. Load a list of properties to check
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ---
    """)
    return


@app.cell
def _(Path, mo):
    # Directory selection for raw data
    base_dir = Path(__file__).parent / "data"

    # Find directories that might contain raw text files
    raw_dir_default = base_dir / "raw"

    dir_input = mo.ui.text(
        value=str(raw_dir_default),
        label="Raw data directory",
        full_width=True,
    )
    dir_input
    return (dir_input,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ---
    """)
    return


@app.cell
def _(mo):
    mo.md(r"""
    ## Preprocessing

    Remove the enacting/amending language as well as page headers and footers; standardize whitespace in the amended text.
    """)
    return


@app.cell
def _(Path, dir_input, mo, raise_md):
    # State for preprocessing
    get_status, set_status = mo.state("")

    def do_preprocess():
        raw_dir = Path(dir_input.value)
        if not raw_dir.exists():
            set_status(f"Directory not found: {raw_dir}")
            return

        # Output to data/processed relative to notebook
        output_dir = Path(__file__).parent / "data" / "processed"
        output_dir.mkdir(parents=True, exist_ok=True)

        txt_files = list(raw_dir.glob("*.txt"))
        if not txt_files:
            set_status(f"No .txt files found in {raw_dir}")
            return

        results = raise_md.process_all_bills(raw_dir, output_dir)
        success_count = sum(1 for v in results.values() if not v.startswith("ERROR"))
        set_status(f"Processed {success_count}/{len(results)} files to {output_dir}")

    preprocess_button = mo.ui.button(
        label="Preprocess",
        on_click=lambda _: do_preprocess(),
    )

    mo.hstack([preprocess_button, mo.md(get_status())], justify="start", gap=2)
    return (preprocess_button,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ---
    """)
    return


@app.cell
def _(Path, mo, preprocess_button):
    # Get list of markdown files and property files
    # Note: depends on preprocess_button to refresh after preprocessing
    _ = preprocess_button

    # Markdown files
    processed_dir = Path(__file__).parent / "data" / "processed"

    def get_md_files():
        if processed_dir.exists():
            return sorted(processed_dir.glob("*.md"))
        return []

    md_files = get_md_files()
    file_options = {f.stem: str(f) for f in md_files if f.stat().st_size > 0}

    # Property files
    specs_dir = Path(__file__).parent / "data" / "specs"

    def get_spec_files():
        if specs_dir.exists():
            return sorted(specs_dir.glob("*.txt"))
        return []

    spec_files = get_spec_files()
    spec_file_options = {f.stem: str(f) for f in spec_files if f.stat().st_size > 0}

    # Build left column (markdown files)
    md_list = mo.md(
        f"**Markdown files in {processed_dir}:**\n\n"
        + "\n".join(f"- {f.name}" for f in md_files)
    )

    # Build right column (property files)
    spec_list = mo.md(
        f"**Property files in {specs_dir}:**\n\n"
        + "\n".join(f"- {f.name}" for f in spec_files)
        if spec_files
        else f"No .txt files found in {specs_dir}"
    )

    mo.hstack([md_list, spec_list], justify="start", gap=4, widths="equal")
    return file_options, spec_file_options


@app.cell
def _(file_options, mo, spec_file_options):
    # File selection dropdowns in a grid
    md_keys = list(file_options.keys()) if file_options else []
    spec_keys = list(spec_file_options.keys()) if spec_file_options else []

    md_dropdown = mo.ui.dropdown(
        options=file_options if file_options else {},
        label="Markdown File",
        value=md_keys[0] if md_keys else None,
    )

    spec_dropdown = mo.ui.dropdown(
        options=spec_file_options if spec_file_options else {},
        label="Property File",
        value=spec_keys[0] if spec_keys else None,
    )

    mo.hstack([md_dropdown, spec_dropdown], justify="start", gap=4, widths="equal")
    return md_dropdown, spec_dropdown


@app.cell
def _(Path, md_dropdown):
    # Load markdown file contents
    def load_file(path_str: str | None) -> str:
        if not path_str:
            return ""
        path = Path(path_str)
        if path.exists():
            return path.read_text()
        return ""

    md_text = load_file(md_dropdown.value)
    return (md_text,)


@app.cell
def _(Path, spec_dropdown):
    # Load property file contents and filter out comments
    def load_spec_file(path_str: str | None) -> str:
        if not path_str:
            return "your properties here"
        path = Path(path_str)
        if path.exists():
            content = path.read_text()
            # Filter out comment lines starting with #
            lines = [
                line for line in content.split("\n") if not line.strip().startswith("#")
            ]
            return "\n".join(lines)
        return "your properties here"

    spec_file_text = load_spec_file(spec_dropdown.value)
    return (spec_file_text,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ---
    """)
    return


@app.cell
def _(mo, spec_file_text):
    # Property input - displays loaded file contents
    property_input = mo.ui.text_area(
        value=spec_file_text,
        label="Properties",
        full_width=True,
        rows=10,
    )
    property_input
    return (property_input,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ---
    """)
    return


@app.cell
def _(mo):
    mo.md(r"""
    ## Verification

    Check whether each property is true, in view of the reference text, with LLM calls.
    """)
    return


@app.cell
def _(llm, md_text, mo, property_input):
    # State for verification results
    get_results, set_results = mo.state(None)
    get_properties, set_properties = mo.state([])

    # Create LLM client once for reuse
    try:
        client = llm.create_client()
    except ValueError as e:
        client = None
        client_error = str(e)
    else:
        client_error = None

    def do_verify():
        if client is None:
            set_results(f"Error: {client_error}")
            set_properties([])
            return
        if not md_text:
            set_results("No file selected")
            set_properties([])
            return
        if not property_input.value.strip():
            set_results("No properties provided")
            set_properties([])
            return

        # Parse properties (one per line, filter out comments)
        properties = [
            p.strip()
            for p in property_input.value.strip().split("\n")
            if p.strip() and not p.strip().startswith("#")
        ]
        results = llm.verify_properties(client, md_text, properties)
        set_properties(properties)
        set_results(results)

    verify_button = mo.ui.button(
        label="Verify Properties",
        on_click=lambda _: do_verify(),
    )

    verify_button
    return get_properties, get_results


@app.cell
def _(get_properties, get_results, mo):
    # Display verification results as a table

    results = get_results()
    properties = get_properties()

    def format_results_table(results, properties):
        if results is None:
            return None
        if isinstance(results, str):
            return mo.md(results)

        rows = []
        for prop, r in zip(properties, results):
            if r.confidence < 0.7:
                flag = status_flag("yellow")
            elif r.satisfied:
                flag = status_flag("green")
            else:
                flag = status_flag("red")

            rows.append(
                {
                    "Status": flag,
                    "Property": prop,
                    "Confidence": f"{r.confidence:.0%}",
                    "Reasoning": r.reasoning,
                }
            )

        return mo.ui.table(rows, selection=None)

    format_results_table(results, properties) if results else None
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ---

    ## Propose Edits

    If one or more of the properties is false, the selected reference test does not meet the spec. Iteratively try to alter the text to make the checks pass, changing as little as possible to do so to preserve the structure and style of the original. At the end of the process, display the final verification status as well as a redline showing the proposed changes against the original text.
    """)
    return


@app.cell
def _(mo):
    # Configuration for edit proposal
    max_iter_slider = mo.ui.slider(
        start=1,
        stop=10,
        value=3,
        step=1,
        label="Max iterations",
    )

    one_by_one_checkbox = mo.ui.checkbox(
        value=False,
        label="Apply properties one-by-one",
    )

    mo.hstack([max_iter_slider, one_by_one_checkbox], justify="start", gap=4)
    return max_iter_slider, one_by_one_checkbox


@app.cell
def _(get_properties, llm, max_iter_slider, md_text, mo, one_by_one_checkbox):
    # State for edit proposal results and working status
    get_edit_result, set_edit_result = mo.state(None)
    get_working, set_working = mo.state(False)

    # Create LLM client for editing
    try:
        edit_client = llm.create_client()
    except ValueError as e:
        edit_client = None
        edit_client_error = str(e)
    else:
        edit_client_error = None

    def do_propose_edits():
        if edit_client is None:
            set_edit_result({"error": edit_client_error})
            return

        properties = get_properties()
        if not properties:
            set_edit_result(
                {"error": "No properties to satisfy. Run verification first."}
            )
            return

        if not md_text:
            set_edit_result({"error": "No file selected"})
            return

        # Set working status
        set_working(True)
        set_edit_result(None)

        # Run the iterative modification
        modified_text, verifications, success, iterations = llm.modify_to_satisfy(
            edit_client,
            md_text,
            properties,
            max_iterations=max_iter_slider.value,
            one_by_one=one_by_one_checkbox.value,
        )

        set_working(False)
        set_edit_result(
            {
                "original": md_text,
                "modified": modified_text,
                "verifications": verifications,
                "properties": properties,
                "success": success,
                "iterations": iterations,
            }
        )

    propose_button = mo.ui.button(
        label="Propose Edits",
        on_click=lambda _: do_propose_edits(),
    )

    working_indicator = mo.md("**Working...**") if get_working() else None

    mo.hstack([propose_button, working_indicator], justify="start", gap=2)
    return (get_edit_result,)


@app.cell
def _(get_edit_result, mo):
    # Display edit status and verification results

    edit_result = get_edit_result()

    def format_verification_summary(result):
        if result is None:
            return None

        if "error" in result:
            return mo.md(f"**Error:** {result['error']}")

        success = result["success"]
        iterations = result["iterations"]
        verifications = result["verifications"]
        properties = result["properties"]

        # Build verification summary
        rows = []
        for prop, v in zip(properties, verifications):
            if v.confidence < 0.7:
                flag = status_flag("yellow")
            elif v.satisfied:
                flag = status_flag("green")
            else:
                flag = status_flag("red")
            rows.append(
                {
                    "Status": flag,
                    "Property": prop,
                    "Confidence": f"{v.confidence:.0%}",
                    "Reasoning": v.reasoning,
                }
            )

        if success:
            return mo.vstack(
                [
                    mo.md(f"### Success after {iterations} iteration(s)"),
                    mo.md("#### Final Verification"),
                    mo.ui.table(rows, selection=None),
                ]
            )
        else:
            return mo.vstack(
                [
                    mo.md(
                        f"### Could not satisfy all properties after {iterations} iteration(s)"
                    ),
                    mo.md("#### Final Verification"),
                    mo.ui.table(rows, selection=None),
                ]
            )

    format_verification_summary(edit_result)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ---
    """)
    return


@app.cell
def _(Path, get_edit_result, mo):
    # Save modified file
    edit_result_for_save = get_edit_result()

    # Default output directory
    output_dir = Path(__file__).parent / "data" / "edited"

    # Only show save UI if we have a successful edit
    show_save = (
        edit_result_for_save is not None
        and "error" not in edit_result_for_save
        and edit_result_for_save.get("success", False)
    )

    get_save_status, set_save_status = mo.state("")

    save_filename = mo.ui.text(
        value="modified.md",
        label="Save as",
        full_width=False,
    )

    def do_save():
        if not show_save:
            set_save_status("No successful edit to save")
            return

        output_dir.mkdir(parents=True, exist_ok=True)
        output_path = output_dir / save_filename.value

        output_path.write_text(edit_result_for_save["modified"])
        set_save_status(f"Saved to {output_path}")

    save_button = mo.ui.button(
        label="Save",
        on_click=lambda _: do_save(),
    )

    # Return UI elements at the end
    mo.vstack(
        [
            mo.hstack([save_filename, save_button], justify="start", gap=2),
            mo.md(get_save_status()),
        ]
    ) if show_save else None
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ---
    #### Proposed Changes (Redline)
    """)
    return


@app.cell
def _(Redlines, get_edit_result, mo):
    # Display redline diff
    edit_result_for_redline = get_edit_result()

    def format_redline(result):
        if result is None:
            return None

        if "error" in result:
            return None

        if not result.get("success", False):
            return mo.md("*No successful edit to display*")

        redline = Redlines(result["original"], result["modified"])
        return mo.md(redline.output_markdown)

    format_redline(edit_result_for_redline)
    return


@app.cell
def _():
    ## Utils
    return


@app.function
def status_flag(status: str) -> str:
    """Return a colored emoji indicator."""
    return {"green": "🟢", "yellow": "🟡", "red": "🔴"}.get(status, "⚪")


@app.cell
def _():
    return


if __name__ == "__main__":
    app.run()
