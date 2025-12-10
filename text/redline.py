# /// script
# requires-python = ">=3.14"
# dependencies = [
#     "altair==6.0.0",
#     "duckdb==1.4.2",
#     "nbformat==5.10.4",
#     "nupunkt==0.6.0",
#     "openai==2.9.0",
#     "polars[pyarrow]==1.36.0",
#     "pytest==9.0.2",
#     "python-lsp-ruff==2.3.0",
#     "python-lsp-server==1.14.0",
#     "redlines==0.6.1",
#     "ruff==0.14.8",
#     "sqlglot==28.1.0",
#     "websockets==15.0.1",
# ]
# ///

import marimo

__generated_with = "0.18.4"
app = marimo.App(width="medium")

with app.setup:
    from redlines import Redlines


@app.cell
def _():
    import marimo as mo
    return (mo,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # Redline

    Demonstrate redlining a text passage loaded from a file.
    """)
    return


@app.cell
def _(mo):
    browser = mo.ui.file_browser(
        initial_path="../data/",
        selection_mode="file",
        multiple=False,
        label="_Please select a file containing the reference text_",
    )
    browser
    return (browser,)


@app.cell
def _(browser):
    file_text = None
    if len(browser.value) > 0:
        with open(browser.value[0].path, "r") as f:
            file_text = regularize(f.read())
    else:
        print("No file selected")

    reference_text = file_text[0] if file_text else ""
    return (reference_text,)


@app.cell
def _(mo, reference_text):
    REF = mo.md(reference_text)
    REF
    return


@app.cell
def _(mo, reference_text):
    WORK = mo.ui.text_area(
        value=reference_text, label="_Working text_", full_width=True
    ).form()
    WORK
    return (WORK,)


@app.cell
def _(WORK, reference_text):
    redline = Redlines(
        reference_text,
        WORK.value,
        # processor=processor
    )
    return (redline,)


@app.cell
def _(mo, redline):
    try:
        REDLINE = mo.md(redline.output_markdown)
    except ValueError:
        REDLINE = mo.md("**No comparison yet**")

    REDLINE
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ---

    ## Utilities
    """)
    return


@app.function
def regularize(text: str) -> list[str] | None:
    """Return a list of paragraphs in `text`, each paragraph stripped of leading and trailing whitespace and with internal line breaks removed. If the text is empty or contains no paragraphs, return None."""
    if not text.strip():
        return None
    paragraphs = [
        p.replace("\n", " ").strip() for p in text.split("\n\n") if p.strip()
    ]
    return paragraphs if paragraphs else None


@app.cell
def _():
    return


if __name__ == "__main__":
    app.run()
