# Main-paper theorem correspondence

This table maps every numbered result in `papers/coefficient-mass.tex` to its
public Lean declaration(s). The declaration types in the named files are the
exact machine-readable hypotheses and conclusions. The repository guards
reject unfinished proofs and unauthorized axioms.

| Result | Lean declaration(s) | Source | Formalized scope |
|---|---|---|---|
| Lemma 2.1 | `consecutiveTail` | `CoefficientMass/Consecutive.lean` | Consecutive certificate and exact tail |
| Theorem 2.2 | `tailBound`, `tailEquality` | `CoefficientMass/Tail.lean`, `CoefficientMass/TailEq.lean` | Displaced-zero bound and equality case |
| Lemma 2.3 | `drive` (with `theta_bound`) | `CoefficientMass/Interlace.lean`, `CoefficientMass/Displaced.lean` | Proved as the internal step `hint` of `drive`, only in the displaced-step configuration of Theorem 2.2 (`V̂ = ηV`, `G_z = 1`), not as a standalone lemma; `theta_bound` is the proof's `σ ≤ τ` step, and `drive` is the inequality `eq:drive` |
| Lemma 3.1 | `certificateWithExclusions_of_tailBound`, `firstRowCertificate` | `CoefficientMass/Certificate.lean`, `CoefficientMass/FirstRow.lean` | Roots at least 2, all `u`: `CertificateWithExclusions`, obtained as `certificateWithExclusions_of_tailBound zeroBound tailBound` in `orderStatistics_of_tailBound` (`Chain.lean`; no standalone headline); `u = 0` with roots above 1: `firstRowCertificate` |
| Theorem 3.2 | `orderStatistics`, `firstRowOrderStatistics` | `CoefficientMass/Chain.lean`, `CoefficientMass/FirstRow.lean` | All rows at roots at least 2; first row above 1 |
| Corollary 3.3 | `complexOrderStatistics_of_orderStatistics`, `complexFirstRowOrderStatistics` | `CoefficientMass/RealPart.lean`, `CoefficientMass/ComplexFirstRow.lean` | All rows when every root is at least 2; first row when every root is greater than 1 |
| Corollary 3.4 | `logarithmicMass` | `CoefficientMass/Chain.lean` | Logarithmic mass bound |
| Corollary 3.5 | `primeRoots` | `CoefficientMass/PrimeCor.lean` | Prime-root lower bound (real `F`; the paper's complex case follows from `logarithmicMass` in the same way) |
| Corollary 3.6 | `primeInfimum` | `CoefficientMass/PrimeCor.lean` | Prime-root infimum with explicit errors |
| Corollary 3.7 | `nearOptimal` | `CoefficientMass/Near.lean` | Comparison with the root product |
| Proposition 4.1 | `unboundedLooseness`, `halfSum`, `looseRatio` | `CoefficientMass/LooseOrder.lean`, `CoefficientMass/LooseRatio.lean` | First-row refinement and ratio; for `r_i = 2 + i L^{-3}` Lean proves `S/(B+1) ≥ L/2`, not the paper's `∼ L`, which suffices for unboundedness |
| Proposition 4.2 | `jensenRows`, `quadraticMass` | `CoefficientMass/QuadMain.lean`, `CoefficientMass/QuadMass.lean` | Jensen rows and quadratic mass |
| Corollary 4.3 | `allRoots` | `CoefficientMass/AllRoots.lean` | Two-sided mass comparison |
| Proposition 4.4 | `sharpRowTwo` | `CoefficientMass/Sharp.lean` | Row-two infimum at `(2,3)` |
| Lemma 5.1 | `rowCertificate` | `CoefficientMass/RowCert.lean` | Confluent row certificate; narrower: assumes a suitable `Z ⊇ S` for every `S` of size `k - 1`, not only for the distances of the `k - 1` largest magnitudes |
| Lemma 5.2 | `deleteLargest` | `CoefficientMass/ConfDel.lean` | Confluent-tail deletion |
| Lemma 5.3 | `holeIntegral` | `CoefficientMass/HoleInt.lean` | Hole integral and bound |
| Lemma 5.4 | `twoHole_weight_le`, `twoHole_integrand` | `CoefficientMass/HoleTwo.lean` | Two-hole estimate |
| Proposition 5.5 | `rowsFree` | `CoefficientMass/HoleFree.lean` | Rows omitting a top-three distance: the `(∗_n)` statement only; the consequence clause for `b_k(F)` has no Lean counterpart, since `rowCertificate` needs every `S` |
| Lemma 5.6 | `holeVals` | `CoefficientMass/ValsMain.lean` | Values at retained holes |
| Lemma 5.7 | `holeTail` | `CoefficientMass/TailBound.lean` | Tail beyond retained holes |
| Proposition 5.8 | `rowsTop` | `CoefficientMass/RowStop.lean` | Rows containing all top-three distances |
| Theorem 5.9 | `everyRow` | `CoefficientMass/RowStop.lean` | Every row for real monic multiples of `(x-2)^L` |

Corollaries 3.5--3.6 use asymptotic notation in the paper; Lean proves
explicit finite inequalities and absolute error bounds instead. Numerical
examples are separately formalized by `workedExamples` in
`CoefficientMass/Examples.lean` and are not premises of the proofs.

Run `lake env lean CoefficientMass.lean` to check the complete import.
`#print axioms CoefficientMass.<name>` on each headline above reports only
the standard Mathlib foundations used here: propositional extensionality,
choice, and quotient soundness. The repository's axiom guard checks this.
