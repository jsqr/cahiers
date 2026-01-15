import marimo

__generated_with = "0.19.2"
app = marimo.App(width="medium")


@app.cell
def _():
    from pathlib import Path

    import marimo as mo
    from redlines import Redlines

    import raise_md
    return Path, Redlines, mo, raise_md


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # Redline Comparison

    Compare two markdown files and display a redline showing the differences.

    1. Select a data directory containing raw `.txt` bill files
    2. Click "Preprocess" to convert them to markdown
    3. Select reference and comparison files to see a redline diff
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

    mo.md(f"**Markdown files in {processed_dir}:**\n\n" + "\n".join(f"- {f.name}" for f in md_files))
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

    reference_dropdown = mo.ui.dropdown(
        options=file_options if file_options else {},
        label="Reference (original)",
        value=keys[0] if keys else None,
    )

    comparison_dropdown = mo.ui.dropdown(
        options=file_options if file_options else {},
        label="Comparison (revised)",
        value=keys[1] if len(keys) > 1 else None,
    )

    mo.hstack([reference_dropdown, comparison_dropdown], justify="start", gap=2)
    return comparison_dropdown, reference_dropdown


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ---
    """)
    return


@app.cell
def _(Path, comparison_dropdown, reference_dropdown):
    # Load file contents
    def load_file(path_str: str | None) -> str:
        if not path_str:
            return ""
        path = Path(path_str)
        if path.exists():
            return path.read_text()
        return ""

    reference_text = load_file(reference_dropdown.value)
    comparison_text = load_file(comparison_dropdown.value)
    return comparison_text, reference_text


@app.cell
def _(Redlines, comparison_text, mo, reference_text):
    # Generate and display redline
    if reference_text and comparison_text:
        redline = Redlines(reference_text, comparison_text)
        output = mo.md(redline.output_markdown)
    else:
        output = mo.md("**Select two files to compare**")

    output
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ---

    ## Legend

    - <span style="color: red; text-decoration: line-through;">Deleted text</span> - Text removed from the reference
    - <span style="color: green; text-decoration: underline;">Added text</span> - Text added in the comparison
    """)
    return


if __name__ == "__main__":
    app.run()
