# /// script
# dependencies = [
#     "marimo",
#     "polars==1.39.3",
# ]
# requires-python = ">=3.14"
# ///

import marimo

__generated_with = "0.23.0"
app = marimo.App(width="medium")

with app.setup:
    import polars as pl


@app.cell
def _():
    import marimo as mo

    return (mo,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Revisiting Knuth's prime number example program.

    This notebook is a loose reconstruction of the program presented in Knuth's 1984 paper introducing Literate Programming [1]. The program, which prints the first thousand primes, is based on an earlier example given by Dijkstra to demonstrate structured programming [2].

    Knuth wrote his program in `WEB`, a language of his own invention that compiles separately into `Pascal` and $\mathrm{\TeX}$ from the same source file. Marimo notebooks don't work quite the same way, although they do support interspersing narrative with code, and presenting programs in an order that supports presentation (Marimo sorts out the dependency graph among cells so they can be written in any order). It's also easy to get the effect of Knuth's `WEAVE` program by toggling Marimo's app view button (`Command-.`).

    Apart from the change in language and the reactive notebook format, I've made a few other changes to avoid something that looks too much like transliterated `Pascal` from the 80s. For example, I consolidate and rearrange sections from the original version, and rely on Python functions instead of `WEB` macros.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## The Program
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### 1. The first thousand primes: plan of the program

    We follow Knuth (and Dijkstra) by beginning with a top-level description of the program. For the most part, we use the same variable names and terminology, and follow the `WEB` pattern in which each section starts with _commentary_ (Markdown cells in our Marimo notebook, like this cell) and proceeds to _program text_ (code cells, like the one below).

    The first real decision is to separate the computation of the prime number table from the formatting routine.

    > Already, there is a break from the Literate Programming spirit! I like to write the type signatures for Python functions, but to do that for `primes()` I need to bring in the `pl.DataFrame` type that only comes up in the commentary for §6.
    """)
    return


@app.function
def primes(m: int = 1000) -> pl.DataFrame:
    """Print the first `m` prime numbers."""
    p = prime_table(m)
    return format_table(p)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### 2. Represent the primes as a list in ascending order

    There are two reasonable approaches for representing data: (i) a sufficiently large array of booleans where the `k`th element is true if and only if `k` is prime, or (ii) an array of the primes themselves in increasing order. We'll choose the second approach, following Dijkstra and Knuth, using Python `list[int]` as a data structure for simplicity.

    > As a side note, this is an example of a section that does not have any program text.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### 3. Generate a table of primes

    We generate entries in the table `p` one at a time: for the `k`th entry, we assume that we have generated the previous `k-1` entries, and call a function to find the next prime in the sequence.
    """)
    return


@app.function
def prime_table(m: int) -> list[int]:
    """Return a list of the first `m` prime numbers."""
    assert m > 0

    p = [2]  # Seed with the first prime; all subsequent primes will be odd
    for _ in range(1, m):
        p.append(next_prime(p))
    return p


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### 4. Find the next prime in the sequence

    An integer $j > 1$ is not prime if and only if there exists a prime number $p_n < j$ such that $j$ is a multiple of $p_n$. Further, if $j$ is not prime its smallest prime factor $p_{small} \le \sqrt j$. This means that we don't have to check divisibility by all of the primes less than $j$; we can stop just before the first prime for which $p_i \gt \sqrt j$ and check $\{p_2 ... p_{i-1}\}$. (We can skip checking divisibility by $p_1 = 2$ by considering only odd numbers.)

    There is a caveat here: we are assuming that all of $\{p_2 ... p_{i-1}\}$ have already been computed by the time we need to check $j \lt p_i^2$.

    But what if for some prime $p_w$ ($w$ for _weird_) it turns out that $p_{w+1} > p_w^2 + 2$? That is to say, what if there is a big gap in the sequence of primes? In that case, after we have computed the primes $\{p_2 ... p_w\}$ we will start our search for the next prime by checking whether $p_w + 2, p_w + 4, ..., p_w^2$ have prime divisors. But when we get to $j^* = p_w^2 + 2$, using the simple logic in line 13 below, we will give up the search too early and incorrectly conclude that $j^* < p_{w+1}$ is prime.

    Fortunately, it turns out from number theory that there are no such gaps in the sequence of primes: $p_k < p_{k-1}^2$ for all $k$ (in fact $p_k < 2 p_{k-1}$).

    > Dijkstra includes a note that he missed this nuance in his first draft, citing a correction from Knuth [2].
    """)
    return


@app.function
def next_prime(p: list[int]) -> int:
    """Assuming that the first `len(p)` primes are already in `p`, in ascending order beginning with index 0,
    return the next prime in the sequence."""
    assert len(p) > 0
    if len(p) == 1:  # so we need only deal with odd primes below
        return 3

    j = p[-1]
    while True:
        j += 2
        for p_i in p[1:]:  # len(p) > 1 if we get to this point
            if p_i * p_i > j:  # see above for number-theoretic justification!
                return j  # we've checked all the plausible candidates, so j is prime
            if j % p_i == 0:  # see §5 for an alternative
                break


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### 5. Check whether $p_i$ is a factor of $j$: the unexpected turn

    We turn next to the problem of checking whether primes are factors. This can be done in Python with a simple check (`if j % p_i ==0: ...`), but in order to better reflect the original algorithm we'd need to do some more work. Knuth supposed that he was programming for a machine with slow or nonexistent division (or remainder) operators. Dijkstra expressly added this limitation as a way to give the algorithm an 'unexpected turn.'

    The idea is to maintain an auxiliary table `mult` to keep track of the odd multiples of each prime in $\{p_2 ... p_{ord}\}$ that are in a 'band' close to the current candidate $j$ ($p_{ord}$ is the smallest prime s.t. $p_{ord}^2 > j$).

    Knuth (and Dijkstra) use a bit of a cheat in determining `ord_max`, the size of the table required for a given `m`: they take advantage of the fixed size `m == 1000` to get `ord_max == 30`, which you can deduce from the prime number theorem $\text{ord} \approx 2 \sqrt{k / \log k}$. Of course, here we are assuming a machine that doesn't even have a remainder function, so that calculation has to be done externally.

    Putting that aside, the advantage of the auxiliary table is that it avoids the need for a remainder operator, and allows efficient checking of divisors without the need to maintain a large table of size `p[m]`, as in the naive implementation of the Sieve of Eratosthenes. The disadvantage is that we would have to significantly refactor the code to get the aux table to work, going back to something closer to the original `ALGOL` or `Pascal` implementations. We leave that as an exercise....
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### 6. Format the table into a polars DataFrame

    Knuth's program seems to have been written for a line printer. It printed out the primes in columns, four to a page, and paginated using a fixed number of rows per page. Here, we do something a little more suited to the Marimo notebook environment, and use the native table display feature. Since it's much simpler to let the built-in table mechanisms worry about pagination, we write out the primes in _rows_.
    """)
    return


@app.function
def format_table(p: list[int], cc: int = 4) -> pl.DataFrame:
    """Display primes in a simple table with cc columns, filled left-to-right, top-down."""

    # Calculate number of rows needed
    num_rows = (len(p) + cc - 1) // cc

    # Pad the list to make it exactly divisible by cc
    padded_p = p + [None] * (num_rows * cc - len(p))

    # Reshape into 2D array (list-of-lists)
    table_data = [padded_p[i * cc : (i + 1) * cc] for i in range(num_rows)]

    column_names = [f"Column {i + 1}" for i in range(cc)]

    return pl.DataFrame(table_data, schema=column_names, orient="row")


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### 6. Run the program and display the results
    """)
    return


@app.cell
def _(mo):
    _df = primes()
    mo.ui.table(_df)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Reflection

    1. Writing out detailed commentary certainly helps to understand a problem and its solution! The two leading examples are the 'caveat' in §4 and the method of checking divisibility without a remainder operation in §5, both of which I would have glossed over if I hadn't taken the time to write out notes.
    2. Dijkstra's program was _already_ a literate program, a decade before the term was coined, in the sense that he included extensive commentary for each step in his development. For that matter, the first published computer program, Ada Lovelace's famous Bernoulli number routine in Note G, is a literate program in the same sense. [3]
    3. Dijkstra, with his interest in process, is more exploratory in his development in that he revises lines of code in the course of building a complete solution. Knuth, by contrast, presents a static result, although with some discussion of alternate paths in the commentary. Perhaps Dijkstra's approach is a more natural fit for those of use who make mistakes and sometimes need to backtrack?
    4. I don't think I would like to go into quite as much detail as either Dijkstra or Knuth on a regular basis. When reading their programs, broken up into 13 pages in Dijkstra's program (without the formatting code!), or 27 sections and 8 columns of text in Knuth's. Dijkstra admits that his is 'too long for [his] taste and wishes', although Knuth seems quite happy with the verbosity: '[t]he extra time I spend in preparing additional commentary is regained because the debugging time is reduced.'
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## References

    [1] D.E. Knuth, Literate Programming. *The Computer Journal* 27:2, 97-111 (1984). [[Link]](http://literateprogramming.com/knuthweb.pdf)

    [2] O.-J. Dahl, E.W. Dijkstra, and C.A.R. Hoare, *Structured Programming*. Academic Press, London and New York (1972). [[Link]](https://archive.org/details/Structured_Programming__Dahl_Dijkstra_Hoare/page/25/mode/2up)

    [3] A. Lovelace, Notes by the Translator, in *Sketch of The Analytical Engine Invented by Charles Babbage,* by L. F. Menabrea. *Taylor's Scientific Memoirs,* 3, 666–731 (1843). [[Link]](https://www.google.com/books/edition/Scientific_Memoirs_Selected_from_the_Tra/qsY-AAAAYAAJ?hl=en&gbpv=1&pg=PA666&printsec=frontcover)
    """)
    return


@app.cell
def _():
    return


if __name__ == "__main__":
    app.run()
