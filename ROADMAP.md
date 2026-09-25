# Roadmap

Research questions the papers leave open.  Each names what is proved and what
is open; an answer lands in the paper it extends, and the row leaves.

## Open at a glance

- [attainment](papers/coefficient-mass-attainment.tex) (`sec:scope`): an a
  priori bound on the zero set minimising one `tau({x})`; a half-mass
  threshold like `thm:halfmass` for `u >= 2`; which root sets below 2 keep
  the escaping placement extremal; the infimum along `(r,3,5,7)` for
  `1 < r < 13/10`, where `thm:family` gives only `<= 209/4`.
- [complex](papers/coefficient-mass-complex.tex): the rows of
  `cor:annuli` item 1 at a fixed separation, and the least such separation
  for the mass (`sec:annuli`).
- [rows](papers/coefficient-mass-rows.tex): whether `nu_2(n) >= nu_1(n)`
  implies the prefix identity at `k = 2` (`sec:secondrow`); whether the
  worst finite position is always small, and failures occur for every
  `1 < r < 2`; closed forms or tree bounds for rows `k >= 3`
  (`sec:finiterows`).
- [sectors](papers/coefficient-mass-sectors.tex): whether `c K**2 log R`
  holds for integer multiples at Gaussian roots in a wide sector
  (`sec:widesectors`); whether one level set `H(y) = -v` holds boundedly
  many Gaussian points above the axis (`prop:gaussheavy`).

## Status

- **Coefficient-mass sharpness, residue.**
  [coefficient-mass-attainment](papers/coefficient-mass-attainment.tex)
  proves the partial-sum criterion at repeated roots (`thm:converse`,
  `cor:charrep`, Descartes at infinity) and non-attainment
  (`thm:noattain`).  When the criterion fails the infimum is `1/T` with
  `T >= tau*` (`thm:value`).  Closed for roots `>= 2`, repeated roots
  included (`sec:extremal`): the escaping placement is the worst one, `T =
  tau*` (`thm:extremal`, `cor:extremalrep`), by lifting the minimiser for
  one fewer exempt coefficient by one node, through the deletion step when
  the new zero is aligned (`lem:delete`) and the run chord when it straddles
  (`prop:runchord`); so the infimum is `min_M max_j |S_j(P_u M)|`, e.g.
  `1704/31` at `(2,3,5,7)`, `u = 1`.  False below 2: at `(11/10,3,5,7)`,
  `u = 1`, a degree-8 multiple has `b_2 = 997/20 < 1704/31 = 1/tau*`
  (`prop:belowtwo`, `tests/test_attainment.py`).  Below 2 (`sec:belowtwo`,
  distinct roots): `T` is a maximum, achieved at some level, `T_0 >= T_1 >= ... >=
  tau*` (`prop:attainT`); a multiplier with exempt positions bounds
  `tau(X)` below (`lem:exemptpair`); for `u = 1` an exact identity for the
  aligned lift makes every placement past an explicit half-mass point `N`
  cheaper than `tau*`, so `T = max(tau*, tau({x}) : x < N)`
  (`thm:halfmass`).  Hence `inf b_2 = 3398808/96935` at `(11/10,3,5,7)`,
  worst placement `{5}`, `N = 11` (`thm:elevenvalue`); along `(r,3,5,7)`
  the escaping placement is extremal exactly for `r >= r_c = 1.4658...`
  (root of `930r^2 - 7r - 1988`), with `inf = 48(r-1)(15r+71)/(49r-34)` on
  `[13/10, r_c]` (`thm:family`: past the half-mass point `N <= 6`, the
  placements 2 and 5 cost less than placement 4); along `(r,5,7)` it fails for every
  `r < 2` (`prop:cutoffsharp`).  Open (`sec:scope`): an a priori bound on
  the zero set minimising one `tau({x})` (to make `u = 1` a finite
  computation outright), a threshold like `N` for `u >= 2`, which root
  sets below 2 keep the escaping placement extremal (it depends on more
  than `r_1`), and the infimum along `(r,3,5,7)` for `1 < r < 13/10`.

- **Coefficient mass at complex roots.**  Purely imaginary pairs are Closed
  ([coefficient-mass-complex](papers/coefficient-mass-complex.tex), split
  out of [coefficient-mass](papers/coefficient-mass.tex); `thm:transfer`,
  `cor:imag`: by multisection a pair `+-ci` is worth exactly one real root
  `c**2`, rows, mass and sharpness included), and the first row holds at
  every root set (`prop:rowone`).  Beyond that no bound can depend on the
  moduli and the angles alone (`prop:noangle`: `x**(2M) + rho**(2M)`).
  At distinct Gaussian-integer pairs (`Im alpha_j >= 1`), integer multiples split into blocks
  (`lem:gausscarry`, `lem:gaussblocks`) each paying `log(rho_min/2)` per
  degree (`thm:gausscharge`).  An Archimedean Newton polygon
  (`thm:archnewton`) gives rows and mass `sum j log(rho_j/3)` for every
  complex multiple with `|f_D| >= 1` once moduli grow by a factor 9 (`cor:separated`), and
  at most `g` moduli per annulus `[R, 9R]` costs a factor `g**2`.  Real roots of both signs (`sec:bothsigns`):
  Rolle on each half-line gives rows charging one root of each sign per
  excluded coefficient (`thm:bothsigns`) and mass
  `floor((L+1)**2/4) log(R/2)`, sharp at `+-s_j` (`cor:bothsignsmass`,
  `prop:bothsignssharp`).  Roots in a sector are treated in
  [coefficient-mass-sectors](papers/coefficient-mass-sectors.tex) (next
  entry).
  Cross terms between annuli (`sec:annuli`): with `K_s` roots of
  modulus in `[T_s, U_s]`, the central index (`lem:central`) charges a
  root once per annulus at or below it.  Dividing out `n` roots of modulus
  `>= T` puts every central index at `r <= T/(3n)` at least `n` below the
  top, and at `r <= T/6` at least `n/2` (`lem:tropcount`; `(x - t)**K`
  shows the factor `n` is needed), so the positions and rows of
  `cor:annuli` item 1 hold once `T_a > 9 n_a U_(a-1)`, `n_a` the roots from
  annulus `a` up.  Closed for the mass at a fixed separation: every
  multiple with `|f_D| >= 1` has mass at least
  `sum_s s K_s log(T_s/2) - S log 2` once `T_1 > 3` and
  `T_a > 162 U_(a-1)` (`thm:fixedgap`: where one central index falls
  short, two share the charge); ratios `log(|beta|/6U_(a-1))` at the
  factor 9 (`cor:annuli` item 2).  A
  lacunary integer multiple at suitable roots attains `sum_s s K_s log t_s`
  exactly, so the constant 1 is sharp as `min T_s -> oo` and the real cross terms `K_s K_t log t` are false,
  also for pairs near the imaginary axis (`prop:annulisharp`).  Open: the
  rows of `cor:annuli` item 1 at a fixed separation, and the least fixed
  separation for the mass (whether 9 suffices).

- **Coefficient mass in sectors.**  The paper is
  [coefficient-mass-sectors](papers/coefficient-mass-sectors.tex), split out
  of [coefficient-mass-complex](papers/coefficient-mass-complex.tex), whose
  block charging at Gaussian roots (`thm:gausscharge`) it uses.  Crowded
  roots in a thin sector are Closed (`lem:sectorcount`, `thm:thinsector`,
  `thm:thingauss`: the argument principle forces a real crossing
  polynomial with `K/2` large roots unless the degree is `>> K/delta`,
  which block charging pays; at such Gaussian roots `thm:thingauss` gives
  order `K**2 log R` when `delta K log(1/delta) = O(1)`).
  Wide sectors (`sec:widesectors`): multiples of degree `O(K)` pay
  `(1/2 - o(1)) K**2 log R` as `K, R -> oo` with `delta K -> 0` (sharp on a
  common ray, `cor:thinconst`) and `(pi/delta - o(1)) K log R` at fixed
  `delta`, `K, R -> oo` (`thm:widesector`, `cor:wideconst`; `x^N - rho^N` attains `pi/delta`, `prop:widesharp`), so
  `c K**2 log R` is false over the reals; at such Gaussian roots and fixed
  `delta`, `(pi/delta - o(1)) K log R` holds at every degree (`cor:widegauss`),
  and, as fewer than `pi (X+1)**2` Gaussian integers have modulus below `X`,
  `(pi/delta - o(1)) K log max(R, sqrt K)` as `K -> oo` uniformly in `R`
  (`cor:gausscount`).
  Two integer imitations of `x^N - rho^N` are limited: `A((x-t)^N)` has at most
  `2 deg A` Gaussian roots above the axis, so `x^N - b` at most two
  (`lem:gaussbinom`); at pairwise coprime odd norms with
  `gcd(a_j, c_j) = 1` a multiple can be `f mod x^m` exactly when
  `P(0)**m | f`, so a gap `m` after the lowest coefficient costs
  `2Km log rho_min`, while at a common norm `n` the lowest `m`
  coefficients can be `n**(K+m-1), 0, ..., 0` (`prop:gausslow`).  A
  multiple `A(x^N)` pays `(N/2) log rho_j` for each root, against
  `N log rho` for all the roots of `x^N - rho^N`; root sets with `-Z = Z`
  (`iZ = Z`), `Z` the roots of `P`, make `P = A(x^2)` (`A(x^4)`) with
  `Lambda(P) <= (1 + o(1)) K**2 log R` (`(1/2 + o(1)) K**2 log R`), so a
  constant `c` in `c K**2 log R` is at most 1, and at most 1/2 when
  `delta > pi/4` (`prop:gausspower`; the root sets lie near one or two
  rays, where `thm:thingauss` gives order `K**2 log R`).  If
  `rho_min > 2` and `b_2(F) < rho_min/2`, `F = x**e (v + H)` with every
  nonleading coefficient of `H` below `rho_min/2`, so all the roots lie in one
  level set `H(y) = -v` (`prop:gaussheavy`); three Gaussian points above the
  axis can share one (`(y**3 - y)**2 = -270400` at `+-7 + 4i`, `8i`, where
  `rho_min = 8`).
  Open: whether `c K**2 log R` holds for all integer multiples at such Gaussian
  roots in a wide sector (the question the introductions of both papers leave),
  and whether the number of Gaussian points above the axis in one such level
  set is bounded.

- **Every row at other roots.**  The paper is
  [coefficient-mass-rows](papers/coefficient-mass-rows.tex), split out of
  [coefficient-mass](papers/coefficient-mass.tex).  The last row is exact
  for every `r > 1` (`cor:lastrowr`), and `thm:tailgen` extends `thm:tail`
  to all roots above 1.  For `1 < r < 2` the rows are pinned up to a
  factor `1 + O(k**(n-1/2) theta**k)` (`thm:prefixrows`, `cor:belowtwo`).
  Crossing (`sec:crossing`): admissible polynomials form a convex set and an insertion flips every
  later sign (`lem:crossing`, `lem:insflip`), so one insertion at the first
  gap covers every later exempted position (`thm:crossing`, all `r > 1`).
  Closed for every root `r >= 2` (`sec:allrowstwo`, `thm:allrowstwo`):
  first-order optimality of a truncated minimizer in one direction bounds
  the insertion at any gap above the constraints (`lem:optins`,
  `lem:truncvertex`), which is the hypothesis of the reduction in the
  proof of `thm:allrowstwo`, so `V_r(L,k) = beta_r(L-k+1)` for all `k`, `L`; for `1 < r < 2` the same
  proof gives `V_r(L,k) >= (r-1)**(k-1) beta_r(L-k+1)`, exact at `k = L`.
  For `1 < r < 2` one polynomial serves every exempted set
  (`sec:onepoly`, `lem:prefixpush`, `thm:onepoly`) and prefix values are
  supermultiplicative (`lem:prefixshift`), so the prefix identity
  `V_r(L,k) = min_(i<=k) 1/nu_i(n)` (`eq:prefixid`) holds for every `k`
  whenever `beta_r(n) <= 1` (`thm:onepolyrows`), in particular for
  `r - 1 <= e**(-4n-2)/C_n` (`lem:topnearone`).  Long diagonals
  (`sec:longdiag`, `lem:farprefix`, `thm:longdiag`,
  `prop:longdiagexplicit`): for each `1 < r < 2` there are `alpha`, `K`
  with the prefix identity holding for `k >= max(K, alpha(n-1))`, so every
  diagonal fails in at most finitely many rows (`cor:longdiagfinite`).
  The second row (`sec:secondrow`): with `eta_sigma(n) = mu_r({sigma}, n+1)`,
  `V_r(n+1,2) = min(1/nu_1(n), min_(sigma < sigma*) 1/eta_sigma(n))` for a
  tail threshold `sigma*` computed from any minimizer of `nu_1(n)`
  (`thm:secondrow`); a candidate optimum for each term can be checked exactly
  for rational `r` by a vertex test (`lem:vertexopt`); and `V_r(L,k)` does not
  increase along a diagonal (`lem:rowmono`).  Exact values
  (`prop:secondrowexact`, `tests/test_rows.py`): `V_{5/4}(16,2) =
  1/nu_3(14) = 6.5694... < beta_{5/4}(15) = 7.6492...`, so the prefix
  identity fails at `(5/4, 16, 2)` and `(5/4, 17, 3)`; `V_{4/3}(19,2) =
  41.38... < beta_{4/3}(18) = 42.34...` with worst position `sigma = 3`;
  and `V_{5/4}(14,2) = beta_{5/4}(13) > 1`, the identity with its minimum
  at `i = 1`, outside `thm:onepolyrows` and `thm:longdiag`.
  Every row (`sec:finiterows`): a threshold for up to `m` far zeros
  (`lem:farzeros`) cuts the exempted sets to a finite tree, so for all
  `r > 1`, `n, m >= 1`, `V_r(n+m,m+1) = min(V_r(n+m-1,m), min_(S in tree)
  1/mu_r(S,n+m))` (`thm:finiterows` (a)); iterating, every row is a finite
  minimum of vertex values.  Part (b) certifies `V_r(n+m,m+1) >= 1/B` from
  upper bounds alone, a finite exact check for rational `r`.  Exact third
  rows (`prop:thirdrowexact`, `tests/test_rows.py`): `V_{4/3}(14,3) =
  7.7168... < V_{4/3}(13,2) = 1/nu_3(11) = 8.5482... < beta_{4/3}(12)`,
  attained only at the pair `{2,3}`, whose optimum omits 1;
  `V_{4/3}(16,3) = 1/nu_4(13) = 14.6268... < V_{4/3}(15,2) =
  beta_{4/3}(14) = min_(i<=4) 1/nu_i(14)`, so the identity fails in the
  third row while holding in the second (and at `k = 4` by `lem:rowmono`);
  `V_{3/2}(10,3) = beta_{3/2}(8)`, the identity with minimum at `i = 1`.
  Open: a proof that `nu_2(n) >= nu_1(n)` implies the identity at `k = 2`
  (conjectured in `sec:secondrow`);
  whether the worst finite position or set is always small; whether failures
  occur for every `1 < r < 2`; closed forms, or bounds on the trees, for the
  rows `k >= 3` with `beta_r(n) > 1` -- `thm:finiterows` does not say how to
  find the minimizers `q_N` it branches on, and its thresholds do not
  decrease with `m`.
