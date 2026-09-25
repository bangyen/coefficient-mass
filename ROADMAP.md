# Roadmap

Research questions the papers leave open.  Each names what is proved and what
is open; an answer lands in the paper it extends, and the row leaves.

- **Coefficient-mass sharpness, residue.**
  [coefficient-mass-attainment](coefficient-mass-attainment.tex)
  proves the partial-sum criterion at repeated roots (`thm:converse`,
  `cor:charrep`, Descartes at infinity) and non-attainment
  (`thm:noattain`).  When the criterion fails the infimum is `1/T` with
  `T >= tau*` (`thm:value`).  CLOSED for roots `>= 2`, repeated roots
  included (`sec:extremal`): the escaping placement is the worst one, `T =
  tau*` (`thm:extremal`, `cor:extremalrep`), by lifting the minimiser for
  one fewer exempt coefficient by one node, through the deletion step when
  the new zero is aligned (`lem:delete`) and the run chord when it straddles
  (`prop:runchord`); so the infimum is `min_M max_j |S_j(P_u M)|`, e.g.
  `1704/31` at `(2,3,5,7)`, `u = 1`.  False below 2: at `(11/10,3,5,7)`,
  `u = 1`, a degree-8 multiple has `b_2 = 997/20 < 1704/31 = 1/tau*`
  (`prop:belowtwo`, `tests/test_attainment.py`).  Open (`sec:scope`): the
  value `T` below 2 (numerically the placement `{5}` there, `~35.06`), and
  for which roots below 2 the escaping placement stays extremal
  (numerically it does at `(3/2,3,5,7)`).

- **Coefficient mass at complex roots.**  Purely imaginary pairs are CLOSED
  ([coefficient-mass-complex](coefficient-mass-complex.tex), split
  out of [coefficient-mass](coefficient-mass.tex); `thm:transfer`,
  `cor:imag`: by multisection a pair `+-ci` is worth exactly one real root
  `c**2`, rows, mass and sharpness included), and the first row holds at
  every root set (`prop:rowone`).  Beyond that no bound can depend on the
  moduli and the angles alone (`prop:noangle`: `x**(2M) + rho**(2M)`).
  At Gaussian-integer pairs, integer multiples split into blocks
  (`lem:gausscarry`, `lem:gaussblocks`) each paying `log(rho_min/2)` per
  degree (`thm:gausscharge`).  An Archimedean Newton polygon
  (`thm:archnewton`) gives rows and mass `sum j log(rho_j/3)` for every
  complex multiple once moduli grow by a factor 9 (`cor:separated`), and
  at most `g` moduli per annulus `[R, 9R]` costs a factor `g**2`.  Crowded
  roots in a thin sector are CLOSED (`lem:sectorcount`, `thm:thinsector`,
  `thm:thingauss`: the argument principle forces a real crossing
  polynomial with `K/2` large roots unless the degree is `>> K/delta`,
  which block charging pays).  Real roots of both signs (`sec:bothsigns`):
  Rolle on each half-line gives rows charging one root of each sign per
  excluded coefficient (`thm:bothsigns`) and mass
  `floor((L+1)**2/4) log(R/2)`, sharp at `+-s_j` (`cor:bothsignsmass`,
  `prop:bothsignssharp`).  Wide sectors (`sec:widesectors`): for multiples of degree `O(K)` the order is
  `min(K**2, K/delta) log R` with both constants sharp (`1/2` of `K**2 log R`
  as `delta K -> 0`, on a common ray; `pi` of `(K/delta) log R`) (`thm:widesector`,
  `cor:wideconst`; `x^N - rho^N` attains `pi/delta`, `prop:widesharp`), so
  `c K**2 log R` is false over the reals; at Gaussian roots
  `(pi/delta - o(1)) K log R` holds unconditionally (`cor:widegauss`).
  Integer imitations of `x^N - rho^N` are not cheap: `A((x-t)^N)` has at most
  `2 deg A` Gaussian roots above the axis, so `x^N - b` at most two
  (`lem:gaussbinom`); at pairwise coprime odd norms with
  `gcd(a_j, c_j) = 1` a multiple can be `f mod x^m` exactly when
  `P(0)**m | f`, so a gap `g` after the lowest coefficient costs
  `2Kg log rho_min`, while at a common norm `n` the lowest `m`
  coefficients can be `n**(K+m-1), 0, ..., 0` (`prop:gausslow`); and an
  exhaustive search finds no `H(x) - v` with small `H` at more than three
  prescribed roots.
  Open: whether `c K**2 log R` holds for all integer multiples at Gaussian
  roots in a wide sector (the question the paper's introduction leaves),
  and whether the cross terms below need a separation growing with the
  root counts.  Cross terms between annuli (`sec:annuli`): with `K_s` roots of
  modulus in `[T_s, U_s]`, the central index (`lem:central`,
  `lem:tropcount`) gives positions charging a root once per annulus at or
  below it (`thm:annuli`), so mass `sum_s s K_s log(T_s/2) - S log 2` once
  `T_a > 3*9**n_a U_(a-1)`, `n_a` the roots from annulus `a` up, and
  ratios `log(|beta|/6U_(a-1))` at the factor 9 (`cor:annuli`).  A
  lacunary integer multiple attains `sum_s s K_s log t_s` exactly, so the
  constant 1 is sharp and the real cross terms `K_s K_t log t` are false,
  also for pairs near the imaginary axis (`prop:annulisharp`).  At a
  constant separation `(x - t)**K` breaks the count of `lem:tropcount`,
  though not necessarily `cor:annuli` item 1.

- **Every row at other roots.**  The paper is
  [coefficient-mass-rows](coefficient-mass-rows.tex), split out of
  [coefficient-mass](coefficient-mass.tex).  The last row is exact
  for every `r > 1` (`cor:lastrowr`), and `thm:tailgen` extends `thm:tail`
  to all roots above 1.  For `1 < r < 2` the rows are pinned up to a
  factor `1 + O(k**(n-1/2) theta**k)` (`thm:prefixrows`, `cor:belowtwo`).
  Crossing (`sec:crossing`): admissible polynomials form a convex set and an insertion flips every
  later sign (`lem:crossing`, `lem:insflip`), so one insertion at the first
  gap covers every later exempted position (`thm:crossing`, all `r > 1`).
  CLOSED for every root `r >= 2` (`sec:allrowstwo`, `thm:allrowstwo`):
  first-order optimality of a truncated minimizer in one direction bounds
  the insertion at any gap above the constraints (`lem:optins`,
  `lem:truncvertex`), which is the hypothesis of the reduction the paper
  inlines, so `V_r(L,k) = beta_r(L-k+1)` for all `k`, `L`; for `1 < r < 2` the same
  proof gives `V_r(L,k) >= (r-1)**(k-1) beta_r(L-k+1)`, exact at `k = L`.
  For `1 < r < 2` one polynomial serves every exempted set
  (`sec:onepoly`, `lem:prefixpush`, `thm:onepoly`) and prefix values are
  supermultiplicative (`lem:prefixshift`), so the prefix identity
  `V_r(L,k) = min_(i<=k) 1/nu_i(n)` (`eq:prefixid`) holds for every `k`
  whenever `beta_r(n) <= 1` (`thm:onepolyrows`), in particular for
  `r - 1 <= e**(-4n-2)/C_n` (`lem:topnearone`).  It is false in general
  for `1 < r < 2`: at `r = 5/4`, `L = 16`, `k = 2` a monic multiple has
  `b_2 <= 6.5695 < 7.6492 <= min_(i<=2) 1/nu_i` (exact rational
  arithmetic, `tests/test_rows.py`).  Long diagonals (`sec:longdiag`,
  `lem:farprefix`, `thm:longdiag`, `prop:longdiagexplicit`): for each
  `1 < r < 2` there are `alpha`, `K` with the prefix identity holding for
  `k >= max(K, alpha(n-1))`, so every diagonal fails in at most finitely
  many rows (`cor:longdiagfinite`).  Open: the value of `V_r(L,k)` for
  `1 < r < 2`, small `k` and `beta_r(n) > 1`, where one polynomial cannot suffice and the prefix
  identity can fail.
