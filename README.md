# coefficient-mass

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22998724.svg)](https://doi.org/10.5281/zenodo.22998724)

Eight papers on how small the coefficients of a polynomial multiple can be
when its roots are prescribed, with executable checks.

If a polynomial `F` is divisible by `(x - r_1) ... (x - r_L)`, its coefficients
cannot all be small: each of the `L` largest nonleading magnitudes is bounded
below, and the bound does not weaken as the multiplier's degree grows.  For
roots at least 2 the `k`-th largest is at least `|f_D| prod_{i>=k} (r_i - 1)`.
The papers prove these bounds, show where they are sharp, and work out what
happens as the roots approach 1 or move off the real line.

| Paper | Subject |
| --- | --- |
| [coefficient-mass](papers/coefficient-mass.tex) | Displaced-zero certificates; the order-statistic tail bound and logarithmic mass (Corollary 3.4) |
| [coefficient-mass-attainment](papers/coefficient-mass-attainment.tex) | Sharpness of the order-statistic bound: the partial-sum criterion, the infimum `1/tau*` at roots `>= 2`, and the placement game below 2 |
| [coefficient-mass-family](papers/coefficient-mass-family.tex) | The placement game along `(r,3,5,7)`: exact infima down to `r -> 1`, where every cost is explicit and the normalised excess oscillates log-periodically |
| [coefficient-mass-rows](papers/coefficient-mass-rows.tex) | Every row is a top row: order statistics of multiples of a power at roots `>= 2` |
| [coefficient-mass-belowtwo](papers/coefficient-mass-belowtwo.tex) | The same rows below the root 2: where the prefix identity holds, and certified failures on intervals |
| [coefficient-mass-complex](papers/coefficient-mass-complex.tex) | Complex roots: exact reductions, arbitrary angles, separated moduli and annuli, and real roots of both signs |
| [coefficient-mass-sectors](papers/coefficient-mass-sectors.tex) | Roots in a sector: thin sectors, sectors of every width, degree charging and integer multiples at Gaussian roots |
| [coefficient-mass-levelsets](papers/coefficient-mass-levelsets.tex) | Light integer multiples at Gaussian roots: one congruence for the lowest coefficients, level sets of a small polynomial, and Pell points |

Open questions are in [ROADMAP](ROADMAP.md).
Cold-machine reproduction instructions are in [ARTIFACT](ARTIFACT.md), and
the main-paper journal package is specified in [SUBMISSION](SUBMISSION.md).

## Checks

```bash
git submodule update --init # fetch the pinned proof guards
uv sync      # pinned dev tools (pytest, ruff)
just check   # lint, spelling and every test (~40s)
just tex     # chktex on the papers (needs chktex)
just sweep   # the coefficient-mass sweep with its printed tallies
just masstwo # the L^2 constant at (x-2)^L, with its tables
just pdf     # build the papers, failing on undefined references (needs tectonic)
just submission # build the self-contained release and JNT submission bundles
```

| Test | Checks |
| --- | --- |
| `tests/test_citations.py` | every numbered citation between the papers names the label it means, by recomputing LaTeX's numbering (`tools/numbering.py`) |
| `tests/test_roadmap.py` | every label the roadmap cites exists in a paper its entry links |
| `tests/test_lean.py` | every result number a Lean docstring cites names the label it means, and each headline Lean theorem proves the statement of the result it is listed against |
| `tests/test_metadata.py` | `CITATION.cff` and `pyproject.toml` carry the same version |
| `tests/test_sweep.py` | the seeded certificate sweep and exact worked numbers of `coefficient-mass` and `-attainment` (`tests/sweep.py`) |
| `tests/test_masstwo.py` | finite checks around the asymptotic Jensen density at `(x-2)^L`, against actual multiples (`tests/masstwo.py`) |
| `tests/test_attainment.py` | exact optima, infima and thresholds along the family `(r,3,5,7)`, and the extremal placement at roots `>= 2` |
| `tests/test_rows.py` | rows and their certified failures below the root 2, from vertex certificates, trees and interval covers (`tests/second_row_cover.json`, `tests/block_row_cover.json`) |
| `tests/test_complex.py` | rows and mass at complex roots: multisection transfer, separated moduli, annuli and Gaussian blocks |
| `tests/test_sectors.py` | sectors of every width, level sets at Gaussian roots, `p`-adic Newton polygons and Pell points |

Each test module's docstring states what that file checks and how, result by
result; the table above is only an index.  Every negative result carries a
control: a false variant the same check must catch.

## Lean

`CoefficientMass/` states the chain from the zero bound for exponential sums
to Corollary 3.4 as `Prop` definitions (`ZeroBound`, `ConsecutiveTail`,
`TailBound`, `CertificateWithExclusions`, `OrderStatistics`,
`ComplexOrderStatistics`, `LogarithmicMass`).  A statement is proved by adding
a theorem of that type; nothing is assumed.  The guards in `scripts/` (the
[lean-guards](https://github.com/bangyen/lean-guards) submodule) reject
unfinished proofs and new axioms, so every commit builds without `sorry` or
extra axioms.

All 23 numbered results of the main paper are proved, along with the equality
case of Theorem 2.2 and the worked examples after it.
[THEOREM_CORRESPONDENCE](THEOREM_CORRESPONDENCE.md) maps each result to its
declaration and file.  The companion papers `coefficient-mass-rows.tex` and
`coefficient-mass-belowtwo.tex` are formalized too, and indexed the same way in
[LEAN](LEAN.md).

For the main chain, `CoefficientMass.logarithmicMass : LogarithmicMass`
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
The stable archive-series DOI is
[doi:10.5281/zenodo.22998724](https://doi.org/10.5281/zenodo.22998724); the
`v1.0.0` release is archived at
[doi:10.5281/zenodo.22998725](https://doi.org/10.5281/zenodo.22998725).
Zenodo metadata for future releases is in `.zenodo.json`.

## License

Papers CC BY 4.0, code MIT; see [LICENSE](LICENSE).  Citation metadata is in
[CITATION.cff](CITATION.cff).
