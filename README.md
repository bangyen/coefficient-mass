# coefficient-mass

Five papers on how small the coefficients of a polynomial multiple can be
when its roots are prescribed, with executable checks.

| Paper | Subject |
| --- | --- |
| [coefficient-mass](papers/coefficient-mass.tex) | Displaced-zero certificates; the order-statistic tail bound and logarithmic mass (Corollary 3.4) |
| [coefficient-mass-attainment](papers/coefficient-mass-attainment.tex) | Sharpness of the order-statistic bound; the partial-sum criterion, the confluent analogue, the infimum `1/tau*` when it fails at roots `>= 2`, and the placement game below 2, down to the limit `r -> 1` along `(r,3,5,7)`, where the normalised excess oscillates log-periodically |
| [coefficient-mass-rows](papers/coefficient-mass-rows.tex) | Every row is a top row: order statistics of multiples of a power |
| [coefficient-mass-complex](papers/coefficient-mass-complex.tex) | Complex roots: exact reductions, arbitrary angles, separated moduli and annuli, real roots of both signs, and degree charging at Gaussian roots |
| [coefficient-mass-sectors](papers/coefficient-mass-sectors.tex) | Roots in a sector: thin sectors, sectors of every width, and integer multiples at Gaussian roots |

Open questions are in [ROADMAP](ROADMAP.md).

## Checks

```bash
uv sync      # pinned dev tools (pytest, ruff)
just check   # lint, spelling and every test (~30s)
just tex     # chktex on the papers (needs chktex)
just sweep   # the coefficient-mass sweep with its printed tallies
just pdf     # build the papers, failing on undefined references (needs tectonic)
```

| Test | Checks |
| --- | --- |
| `tests/test_citations.py` | every numbered citation between the papers names the label it means, by recomputing LaTeX's numbering (`tools/numbering.py`) |
| `tests/test_roadmap.py` | every label the roadmap cites exists in a paper its entry links |
| `tests/test_lean.py` | every result number a Lean docstring cites names the label it means, and each headline Lean theorem proves the statement of the result it is listed against |
| `tests/test_metadata.py` | `CITATION.cff` and `pyproject.toml` carry the same version |
| `tests/test_sweep.py` | the seeded certificate sweep and exact worked numbers of `coefficient-mass` and `-attainment` (`tests/sweep.py`) |
| `tests/test_attainment.py` | the infimum `1704/31` at `(2,3,5,7)` approached by exact optima up to degree 30, with the constant term the best exempt position, the run chord behind the extremal escaping placement at roots `>= 2` (failing above the cutoff), the exact infimum `1704/31` at `(2,3,5,7)`, the multiple beating `1/tau*` at `(11/10,3,5,7)`, the aligned-lift identity at any roots above 1, the exact infimum `3398808/96935` at `(11/10,3,5,7)`, the threshold `r_c` along `(r,3,5,7)`, the infimum `beta(r)` there on `[13/10, r_c]` and in seven pieces on `[1.0745..., 13/10]` (Sturm counts over Q), the closed forms at `(3,5,7)` and the flipped witness behind `inf b_2 - 24 ~ (r-1)^alpha` near `r = 1`, the two sides of `3^x (r-1) = 18` behind its oscillation and the exact infimum at `r = 5701/5700` (zero set `{1,10,1335}`), and the failure along `(r,5,7)` for every `r < 2` |
| `tests/test_rows.py` | last rows, every row a top row at `r >= 2` on a window, the exact `r = 5/4` counterexample to the prefix identity, exact second rows at `r = 5/4` and `4/3` from vertex certificates, the exact `r = 177/167` failure of the prefix identity although `nu_2(50) > nu_1(50)`, second-row failures at every `r` in `[21/20, 139/100]` from 49 interval certificates (`tests/second_row_cover.json`), far-zero thresholds, and exact third rows at `r = 4/3` and `3/2` from certified trees |
| `tests/test_complex.py` | multisection transfer, imaginary pairs, first row at Gaussian roots, Newton-polygon dominance and separated moduli, several annuli (with the rows failing at separation `n_a` and the mass bound just above separation 2, and both holding at `3 rho_(n_a)` with few roots above a gap), truncations of `prod (1 - x/beta)^(-1)` bounded below and the second row at separation `n_2 + 1` (linear in `lambda`, constant tending to 1 as `|alpha|` grows), a second position below the gap and the rows and mass for two annuli at `max(4, n_2 + 1)` (failing just above `n_2`), every row at separation `n_a + 9`, and at `n_a + 1` above 30 roots by eliminating at two lower zeros, with the row 3 failing when only the top separation grows or both are below `n_a + 1/2`, both signs, and Gaussian blocks, on seeded integer multiples and exact optima |
| `tests/test_sectors.py` | real crossings next to a sector (Sturm counts), thin and wide sectors, the sharp constant at `x^N - rho^N`, integer imitations of `x^N - rho^N`, polynomials in a power and symmetric root sets, heavy coefficients and level sets at Gaussian roots, `p`-adic Newton polygons at the primes over coprime norms and small coefficients after the lowest one and the one congruence cutting out the lowest coefficients, the three-point level sets from a Pell equation and the circle they lie near, the Newton polygon at each prime of a level set (at most `ord_0 H` points per norm), symmetries of a level set (a unit relating two of its points is a symmetry of `H`) and the classes of one norm, and Gaussian integers in a disc and a half-annulus |

Each negative result carries a control: a false variant the same check must
catch.

## Lean

`CoefficientMass/` states the chain from the zero bound for exponential sums
to Corollary 3.4 as `Prop` definitions (`ZeroBound`, `ConsecutiveTail`,
`TailBound`, `CertificateWithExclusions`, `OrderStatistics`,
`ComplexOrderStatistics`, `LogarithmicMass`).  A statement is proved by adding
a theorem of that type; nothing is assumed.  The guards in `scripts/` (the
[lean-guards](https://github.com/bangyen/lean-guards) submodule) reject
unfinished proofs and new axioms, so every commit builds without `sorry` or
extra axioms.

Everything is proved: `CoefficientMass.logarithmicMass : LogarithmicMass`
depends only on the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`).  Lemma 2.3 and the bound `σ ≤ G_z / V̂_z` use weak sign
alternation (`card_le_of_alternating`, a mean-value-theorem induction), as in the
paper; the formal zero bound counts distinct zeros only, and the sign
changes at prescribed zeros come from weak alternation.

```bash
git submodule update --init
lake exe cache get
just lean
```

## Citing from elsewhere

These papers began in [bangyen/esolangs](https://github.com/bangyen/esolangs),
where the Polynomial language's lower bound rests on Corollary 3.4.  That repo
cites a tagged version and pins the result numbers it uses.  After a change
that renumbers a cited result, tag a new version and regenerate the pins:

```bash
just pin coefficient-mass:3.4 coefficient-mass-complex:2.1
```

Pushing a tag `vN` (or `vN.M.K`) runs the release workflow: it checks the tag
against the version in `pyproject.toml`, runs the checks, and attaches the
compiled papers to a GitHub release, so a cited version keeps its PDFs.
With the repository's Zenodo integration switched on, each release is also
archived under a DOI (metadata in `.zenodo.json`); cite that DOI from the
papers' data availability statements.

## License

Papers CC BY 4.0, code MIT; see [LICENSE](LICENSE).  Citation metadata is in
[CITATION.cff](CITATION.cff).
