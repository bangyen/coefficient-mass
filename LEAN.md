# Companion-paper Lean index

`THEOREM_CORRESPONDENCE.md` maps the main paper, `papers/coefficient-mass.tex`,
to its Lean declarations. This file does the same for the two companion papers
that are formalized. The declaration types in the named files are the exact
machine-readable hypotheses and conclusions; the repository guards reject
unfinished proofs and unauthorized axioms.

## `coefficient-mass-rows.tex`

Formalized from its start; Sections 2, 4 and 5 in full.

| Result | Lean declaration(s) | Source | Formalized scope |
|---|---|---|---|
| Proposition 2.1 | `rowValueCert`, `rowValueDual`, `rowValueTop` | `CoefficientMass/RowValue.lean`, `CoefficientMass/RowValueDual.lean`, `CoefficientMass/RowFar.lean` | Certificate at a root `r > 1`; `V_r(L, k) = inf 1/μ_r(S, L)` by Hahn--Banach separation and truncation; `V_r(L, k) ≤ β_r(L - k + 1)` |
| Theorem 2.2 | `tailBoundGen` | `CoefficientMass/TailGen.lean` | General tail bound |
| Lemma 2.3 | `confDeleteR` | `CoefficientMass/ConfPrefix.lean` | Confluent deletion at a root `r` |
| Corollary 2.4 | `lastRow` | `CoefficientMass/RowLast.lean` | Last row |
| Lemma 3.1 | `intZerosInf` | `CoefficientMass/IntZerosInf.lean` | Integer zero sets suffice for the dual infimum |
| Lemma 3.2 | `rowPointwise` | `CoefficientMass/RowPointwise.lean` | Pointwise row comparison |
| Theorem 3.3 | `prefixRows` | `CoefficientMass/RowPrefixRows.lean` | Prefix rows |
| Lemma 3.4 | `nbMass` | `CoefficientMass/NbMass.lean` | Mass bound, via Chebyshev's inequality from the moments of the negative-binomial law |
| Corollary 3.5 | `belowTwo` | `CoefficientMass/BelowTwo.lean` | Rows below the root 2 |
| Lemma 4.1 | `crossing` | `CoefficientMass/Crossing.lean` | Crossing lemma |
| Lemma 4.2 | `insFlip` | `CoefficientMass/Insert.lean` | Insertion flip |
| Theorem 4.3 | `crossRows` | `CoefficientMass/CrossRows.lean` | Rows from crossings |
| Lemma 4.4 | `prefixPush` | `CoefficientMass/PrefixPush.lean` | Prefix push |
| Lemma 5.1 | `truncVertex` | `CoefficientMass/TruncVertex.lean` | Truncation at a vertex certificate |
| Lemma 5.2 | `optIns`, `optInsMax` | `CoefficientMass/OptIns.lean` | Optimal insertion and its maximum |
| Theorem 5.3 | `allRowsTwo` | `CoefficientMass/AllRowsTwo.lean` | Every row at `r ≥ 2`, with `V_r(L, k) = β_r(L - k + 1)` |
| (Section 5) | `prefixUp` | `CoefficientMass/PrefixUp.lean` | `ν_{i+1}(n) ≤ ν_i(n)/(r - 1)` |

## `coefficient-mass-belowtwo.tex`

The rows below the root 2, formalized through its hand-proved results.

| Result | Lean declaration(s) | Source | Formalized scope |
|---|---|---|---|
| Theorem 2.1 | `onePoly` | `CoefficientMass/OnePoly.lean` | The one-polynomial bound |
| Lemma 2.2 | `prefixShift` | `CoefficientMass/PrefixShift.lean` | Prefix shift |
| Theorem 2.3 | `onePolyRows` | `CoefficientMass/OnePolyRows.lean` | Rows from one polynomial |
| Lemma 2.4 | `topNearOne` | `CoefficientMass/TopNearOne.lean` | Top row near the root 1 |
| Lemma 3.1 | `farPrefix` | `CoefficientMass/FarPrefix.lean` | Far prefix |
| Theorem 3.2 | `longDiag` | `CoefficientMass/LongDiag.lean` | Long diagonal |
| Proposition 3.3 | `longDiagExplicit` | `CoefficientMass/LongDiagExplicit.lean` | Explicit form |
| Corollary 3.4 | `longDiagFinite` | `CoefficientMass/LongDiagExplicit.lean` | Finite consequence |
| Lemma 4.1 | `rowMono` | `CoefficientMass/RowMono.lean` | Row monotonicity |
| Lemma 4.2 | `vertexOpt` | `CoefficientMass/VertexExists.lean` | Vertex optimality |
| Theorem 4.3 | `secondRow`, `exists_muR_min` | `CoefficientMass/SecondRow.lean`, `CoefficientMass/MuRMin.lean` | The second row; every `μ_r(S, L)` is attained |
| Lemma 4.6 | `rootMono` | `CoefficientMass/RootMono.lean` | Monotonicity in the root |
| Lemma 5.1 | `farZeros` | `CoefficientMass/FarZeros.lean` | Far zeros |
| Theorem 5.2 | `finiteRows` | `CoefficientMass/FiniteRowsAll.lean` | Finitely many rows |
| Lemma 5.4 | `exemptBlock` | `CoefficientMass/BlockBound.lean` | Exempt block |
