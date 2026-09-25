# coefficient-mass

Four papers on how small the coefficients of a polynomial multiple can be
when its roots are prescribed, with executable checks.

| Paper | Subject |
| --- | --- |
| [coefficient-mass](coefficient-mass.tex) | Displaced-zero certificates; the order-statistic tail bound and logarithmic mass (Corollary 3.4) |
| [coefficient-mass-attainment](coefficient-mass-attainment.tex) | Sharpness of the order-statistic bound; the partial-sum criterion and the confluent analogue |
| [coefficient-mass-rows](coefficient-mass-rows.tex) | Every row is a top row: order statistics of multiples of a power |
| [coefficient-mass-complex](coefficient-mass-complex.tex) | Complex roots, real roots of both signs, and sectors |

Open questions are in [ROADMAP](ROADMAP.md).

## Checks

```bash
just check   # lint, cross-reference test, certificate sweep
just pdf     # build the papers (needs tectonic)
```

- `tests/test_citations.py` recomputes each paper's LaTeX numbering and holds
  every numbered citation between the papers to the label it means.
- `tests/sweep.py` is a seeded certificate sweep plus exact rational checks of
  every number the papers work out by hand (~2s).

## Citing from elsewhere

These papers began in [bangyen/esolangs](https://github.com/bangyen/esolangs),
where the Polynomial language's lower bound rests on Corollary 3.4.  That repo
cites a tagged version and pins the result numbers it uses.  After a change
that renumbers a cited result, tag a new version and regenerate the pins:

```bash
just pin coefficient-mass:3.4 coefficient-mass-complex:2.1
```
