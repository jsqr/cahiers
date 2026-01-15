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

    return Path, llm, mo, raise_md


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # Check properties and edit to satisfy them

    Load a Markdown document, then check it against a sequence of properties. If any fail, attempt to make changes until all properties are satisfied.

    1. Select a data directory containing raw `.txt` bill files
    2. Click "Preprocess" to convert them to markdown
    3. Select a file
    4. Enter properties
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
    # Get list of markdown files in data/processed
    # Note: depends on preprocess_button to refresh after preprocessing
    _ = preprocess_button
    processed_dir = Path(__file__).parent / "data" / "processed"

    def get_md_files():
        if processed_dir.exists():
            return sorted(processed_dir.glob("*.md"))
        return []

    md_files = get_md_files()
    file_options = {f.stem: str(f) for f in md_files if f.stat().st_size > 0}

    mo.md(
        f"**Markdown files in {processed_dir}:**\n\n"
        + "\n".join(f"- {f.name}" for f in md_files)
    )
    return (file_options,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ---
    """)
    return


@app.cell
def _(file_options, mo):
    # File selection dropdowns
    keys = list(file_options.keys()) if file_options else []

    md_dropdown = mo.ui.dropdown(
        options=file_options if file_options else {},
        label="File",
        value=keys[0] if keys else None,
    )

    md_dropdown
    return (md_dropdown,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ---
    """)
    return


@app.cell
def _(Path, md_dropdown):
    # Load file contents
    def load_file(path_str: str | None) -> str:
        if not path_str:
            return ""
        path = Path(path_str)
        if path.exists():
            return path.read_text()
        return ""

    md_text = load_file(md_dropdown.value)
    return (md_text,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ---
    """)
    return


@app.cell
def _(Path, mo):
    # Get list of property files in data/specs
    specs_dir = Path(__file__).parent / "data" / "specs"

    def get_spec_files():
        if specs_dir.exists():
            return sorted(specs_dir.glob("*.txt"))
        return []

    spec_files = get_spec_files()
    spec_file_options = {f.stem: str(f) for f in spec_files if f.stat().st_size > 0}

    mo.md(
        f"**Property files in {specs_dir}:**\n\n"
        + "\n".join(f"- {f.name}" for f in spec_files)
        if spec_files
        else f"No .txt files found in {specs_dir}"
    )
    return (spec_file_options,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ---
    """)
    return


@app.cell
def _(mo, spec_file_options):
    # Property file selection dropdown
    spec_keys = list(spec_file_options.keys()) if spec_file_options else []

    spec_dropdown = mo.ui.dropdown(
        options=spec_file_options if spec_file_options else {},
        label="Property File",
        value=spec_keys[0] if spec_keys else None,
    )

    spec_dropdown
    return (spec_dropdown,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ---
    """)
    return


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
    return get_results, get_properties


@app.cell
def _(get_properties, get_results, mo):
    # Display verification results as a table
    def status_flag(status: str) -> str:
        """Return a colored emoji indicator."""
        return {"green": "🟢", "yellow": "🟡", "red": "🔴"}.get(status, "⚪")

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


@app.cell
def _():
    return


if __name__ == "__main__":
    app.run()
