# coefficient-mass

Four papers on how small the coefficients of a polynomial multiple can be
when its roots are prescribed, with executable checks.

| Paper | Subject |
| --- | --- |
| [coefficient-mass](coefficient-mass.tex) | Displaced-zero certificates; the order-statistic tail bound and logarithmic mass (Corollary 3.4) |
| [coefficient-mass-attainment](coefficient-mass-attainment.tex) | Sharpness of the order-statistic bound; the partial-sum criterion, the confluent analogue, and the infimum `1/tau*` when it fails |
| [coefficient-mass-rows](coefficient-mass-rows.tex) | Every row is a top row: order statistics of multiples of a power |
| [coefficient-mass-complex](coefficient-mass-complex.tex) | Complex roots, real roots of both signs, and sectors |

Open questions are in [ROADMAP](ROADMAP.md).

## Checks

```bash
uv sync      # pinned dev tools (pytest, ruff)
just check   # lint and every test (~10s)
just sweep   # the coefficient-mass sweep with its printed tallies
just pdf     # build the papers, failing on undefined references (needs tectonic)
```

| Test | Checks |
| --- | --- |
| `tests/test_citations.py` | every numbered citation between the papers names the label it means, by recomputing LaTeX's numbering (`tools/numbering.py`) |
| `tests/test_roadmap.py` | every label the roadmap cites exists in a paper its entry links |
| `tests/test_sweep.py` | the seeded certificate sweep and exact worked numbers of `coefficient-mass` and `-attainment` (`tests/sweep.py`) |
| `tests/test_attainment.py` | the run chord behind the extremal escaping placement at roots `>= 2` (failing above the cutoff), the exact infimum `1704/31` at `(2,3,5,7)`, and the multiple beating `1/tau*` at `(11/10,3,5,7)` |
| `tests/test_rows.py` | last rows, every row a top row at `r >= 2` on a window, the exact `r = 5/4` counterexample to the prefix identity, and exact second rows at `r = 5/4` and `4/3` from vertex certificates |
| `tests/test_complex.py` | multisection transfer, imaginary pairs, first row at Gaussian roots, several annuli, both signs, and wide sectors, on seeded integer multiples and exact optima |

Each negative result carries a control: a false variant the same check must
catch.

## Lean

`CoefficientMass/` states the chain from the zero bound for exponential sums
to Corollary 3.4 as `Prop` definitions (`ZeroBound`, `ConsecutiveTail`,
`TailBound`, `CertificateWithExclusions`, `OrderStatistics`,
`ComplexOrderStatistics`, `LogarithmicMass`).  A statement is proved by adding
a theorem of that type; nothing is assumed.  The guards in `scripts/` (the
[lean-guards](https://github.com/bangyen/lean-guards) submodule) reject
unfinished proofs and new axioms, so the build is honest at every commit.

Everything is proved: `CoefficientMass.logarithmicMass : LogarithmicMass`
depends only on the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`).  One step departs from the paper: Lemma 2.3 and the bound
`σ ≤ G_z / F̂_z` use weak sign alternation (`card_le_of_alternating`, a
mean-value-theorem induction) in place of zero counting with multiplicity and
the asymptotic argument.

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

## License

Papers CC BY 4.0, code MIT; see [LICENSE](LICENSE).  Citation metadata is in
[CITATION.cff](CITATION.cff).
