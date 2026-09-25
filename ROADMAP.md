# Roadmap

Research questions the papers leave open.  Each names what is proved and what
is open; an answer lands in the paper it extends, and the row leaves.

## Open at a glance

- [attainment](papers/coefficient-mass-attainment.tex) (`sec:scope`): an a
  priori bound on the zero set minimising one `tau({x})`; a half-mass
  threshold like `thm:halfmass` for `u >= 2`; which root sets below 2 keep
  the escaping placement extremal; the pieces along `(r,3,5,7)` for
  `1 < r < 1.0745...`, where `thm:familylow` stops (infinitely many
  accumulate at `r = 1` by `cor:familyone`; near 1, off the jumps, the
  worst placement is `x*` with zero set `{1,x*,z}` by `thm:familyosc`, but
  which `z`, and the transition near the jumps, are open).
- [complex](papers/coefficient-mass-complex.tex): the least fixed
  separation for the mass, between `2 + 1/18915` and 81 (at most 9 for two
  annuli with `n_2 <= 8`, `cor:rowstwo`), and whether 9 suffices; whether
  `T_a > (n_a + 1) U_(a-1)` gives every row of `cor:annuli` also where
  `n_a < 30` (it does where `n_a >= 30`, and for large `n_a` the additive
  constant is exactly 1/2, `cor:rowsplusone`, `prop:rowslower`; below 30
  only `min(n_a + 9, 3 rho_(n_a))` is known, `cor:rowsall`); the best
  constant `c` in `b_2 >= c lambda (1 - 1/|alpha|) |f_D| prod |beta|` for
  `|alpha|` near 1 (in `[1/8, 1]`; at least `1 - 1/a_0` over
  `|alpha| >= a_0 >= 2`, `prop:rowstwolarge`).
- [rows](papers/coefficient-mass-rows.tex): a condition giving the prefix
  identity at `k = 2` (`nu_2(n) >= nu_1(n)` does not, `prop:secondrowhyp`);
  whether the worst finite position is always small, and failures occur
  for every `1 < r < 2`; closed forms or tree bounds for rows `k >= 3`
  (`sec:finiterows`).
- [sectors](papers/coefficient-mass-sectors.tex): whether `c K**2 log R`
  holds for integer multiples at Gaussian roots in a wide sector
  (`sec:widesectors`); whether one level set `H(y) = -v` holds a number of
  Gaussian points above the axis bounded independently of `rho_min` (fewer
  than `6 rho_min` by `prop:gausscircle`, at most `ord_0 H` per norm by
  `prop:gaussprimes`), and whether one norm carries at most two; whether
  small coefficients after the lowest one cost nearly as much as zeros at
  pairwise coprime norms (`prop:gaussadic`).

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
  placements 2 and 5 cost less than placement 4).  Below 13/10
  (`thm:familylow`), one multiplier per zero set (`eq:witness`: the
  witness of a full certificate bounds `tau({x})` exactly while its entries
  on the zero set stay in `[-1, 1]`) gives the infimum on
  `[1.0745..., 13/10]` in seven rational pieces: placement 5 with zero sets
  `{1,4,5}`, `{1,3,5}`, then from `1.1244...` placement 4 with `{1,4,8}`,
  `{1,4,7}`, `{1,4,6}`, `{1,4,5}`, `{1,3,4}` (so `beta(r)` already from
  `1.2741...`); `N <= 13`, the other placements beaten by the aligned lifts
  `{1,3,x}` and by `{1,2,13}`, `{1,2,10}`, every sign on an interval a
  Sturm count over Q; e.g. `314024/7627` at `r = 5/4`.  Near `r = 1`
  (`thm:familyone`): the placements at `(3,5,7)` have closed forms in
  `3**-x, 5**-x, 7**-x` (`lem:threenode`: the certificate `{1,x}` costs
  `t(x)`, with `1/24 - t(x)` between `(3/5)**x/16` and `(3/5)**x/6`); a
  witness with one sign flip far out keeps
  `tau({x}) >= t(x)/(1 + 3**(3-x))` while `3**x <= 8/(r(r-1)) - 48`, and
  past `log_3(1/(r-1)) + 6` the certificate `{1,2,x}` costs at most
  `5/192`.  So `inf b_2 > 24` for every `1 < r < 3`, and for
  `1 < r <= 101/100`
  `24 + (3/2) eps**alpha <= inf b_2 <= 24 + 125 eps**alpha`,
  `eps = r - 1`, `alpha = log(5/3)/log 3 = 0.46497...`, with every worst
  placement within `(-3, 6)` of `log_3(1/eps)`; `tau({x}) -> t(x)` for each
  `x >= 4`.  Hence the limit is 24 (the value at `(3,5,7)`), the worst
  placement tends to infinity, and `T` agrees with no finite set of
  rational functions near 1, so infinitely many pieces accumulate there
  (`cor:familyone`).  The constant does not converge (Closed, negatively;
  `lem:eighteen`, `thm:familyosc`): with `x*` the largest integer with
  `3**x* (r-1) < 18`, the witness with the flip corrected at positions 1
  and `x` makes `tau({x}) = t(x) - O(3**-x)` exactly, with minimising zero
  set `{1,x,z}`, while `3**x (r-1) < 18`, and above 18 the certificate
  `U^(c)` plus a small weight on `1/r` costs about
  `t(c) + ell(c)/(3**x (r-1)) < 1/24 - eta` (as
  `K_c = ell(c)/(1/24 - t(c)) > 18`, `K_c -> 18`).  So off neighbourhoods
  of the jumps `{x*}` is the only worst placement,
  `inf b_2 - 24 = (80 + o(1))(3/5)**x*`, and
  `(inf b_2 - 24)(r-1)**(-alpha)` oscillates log-periodically: its limit
  points fill `[80 * 18**(-alpha), (400/3) 18**(-alpha)] = [20.865...,
  34.775...]`, the limit along `r = 1 + 18 * 3**(-n-w)` being
  `80 * 18**(-alpha) (5/3)**w`.  Exactly at `r = 5701/5700`:
  `T = tau({10})`, the tail of `{1,10,1335}`, `inf b_2 = 24.4788...`
  (`tests/test_attainment.py`).  Along `(r,5,7)` it fails for every `r < 2`
  (`prop:cutoffsharp`).  Open (`sec:scope`): an a priori bound on the zero
  set minimising one `tau({x})` (to make `u = 1` a finite computation
  outright), a threshold like `N` for `u >= 2`, which root sets below 2
  keep the escaping placement extremal (it depends on more than `r_1`),
  the pieces along `(r,3,5,7)` on `(1, 1.0745...)` themselves (which `z` in
  `{1,x*,z}`: a piece ends where the witness entry `s_z` reaches `+-1`), an
  explicit range of `r` in `thm:familyosc` (a), and the transition near the
  jumps, where `x*` and `x* + 1` compete (numerically with zero sets
  `{1,c,x*+1}`, `c = 3, 4`; at `r = 101/100` the worst placement is 7, not
  `x* = 6`): whether the constant minus its limit function tends to 0
  uniformly for `0 < w <= 1 - delta`, and whether `tau({x})` tends to
  `min_c (t(c) + ell(c)/kappa)` when `3**x (r-1) -> kappa > 18`.

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
  annulus `a` up.  Exactly, the full count holds for `T > rho_n r`, `rho_n`
  the reciprocal of the root of `(1 + theta)**n - 1 = (1 - theta)**n`:
  `rho_1 = 2` (sharp: `x**D - sum_(i<D) x**i`), `rho_2 = 4`,
  `rho_n < 7n/3`, `rho_n/n -> 1/arsinh(1/2) = 2.078...`; so the rows hold
  once `T_a > 3 rho_(n_a) U_(a-1)`, in particular `T_a > 7 n_a U_(a-1)`
  (`cor:fewabove`).  Closed negatively for the rows at a fixed separation:
  `(x - q)(x + Kq)**K`, `K >= 10`, `q >= 4**K`, has `T_2 = n_2 U_1`,
  `f_1 = 0` (the `K` zeros above cancel the one below) and
  `b_2 < 2**K (Kq)**(K-1)`, below the row `k = 2` by a factor tending to 0
  (`prop:rowsneedn`); so the rows need a separation between `n_a` and
  `9 n_a`, at `3 rho_(n_a) < 7 n_a` by `cor:fewabove`, where the full
  count `D - y >= n` of `lem:tropcount` holds exactly when `T > rho_n r`,
  and at `n_a + 9` (`cor:rowsall`, below).
  For two annuli `n_2 + 1` suffices (`thm:rowstwo`,
  `cor:rowstwo`): dividing out the `n` zeros above leaves at a lower zero
  `alpha` the truncation `sum_(k<=M) h_k(alpha/beta)`, of modulus at least
  `lambda = 1 - n|alpha|/T` (`lem:trunc`: the uniform average on the simplex
  turns it into `binom(n+k-1,k)`-weighted partial sums, whose real part is
  at least `1 - n|y|` by two summations by parts); so
  `b_2 >= (lambda**2/2)(1 - 1/|alpha|) |f_D| prod |beta|` whenever
  `|alpha| < T/n`, and at `T_2 >= C n_2 U_1` the second row holds up to
  `(1 - 1/C)**2/3`, independent of `n_2`, so `C = 1` is the least constant
  in that form.  This also gives row 2 for every `S`, and for `S = 2`,
  `n_2 <= 8` the mass bound of `thm:fixedgap` at the separation 9.  The
  factor `lambda**2` improves to `lambda gamma / 2`, `gamma =
  (1 - |alpha|/T)**n >= max(lambda, 1/4)` (`gamma = 1` for `n = 1`, where
  the proof uses both zeros directly), so `b_2 >= (lambda/8)(1 - 1/|alpha|)
  |f_D| prod |beta|`, of the sharp order `lambda`.  Rows `k >= 3`
  (`lem:rowsbelow`, `thm:rowsk`, `cor:rowsall`): the central indices at
  radii below the `(k-1)`-st annulus give `k - 1` positions carrying
  `A_(>=k)` once `T_k > rho_(n_k) r` (so the row `k` needs `3 rho_(n_k)`
  only at the `k`-th separation, and 9 below it); at a zero `alpha` of the `(k-1)`-st annulus the
  truncation gives the last one, the central index at `r` just above
  `3 U_(k-2)` bounding the lower positions there, whenever
  `lambda (1 - 2 xi) > (1 - lambda) xi/(1 - xi)`, `xi = 3 U_(k-2)/T_(k-1)`;
  so every row and the mass hold at `T_a > min(n_a + 9, 3 rho_(n_a)) U_(a-1)`,
  which is `n_a + 9` for `n_a >= 2` (any `c > 3` in place of 9 once `n_k` is
  large), superseding `7 n_a` for `n_a >= 2`.  The lower separation must grow too:
  `(x - q_1)(x - q_2)(x + t)**K` with `t = (K + h) q_2`,
  `q_2/q_1 = K(K+1+2h)/(2h(K+h)) < n_2/(2h) + 1` has `f_2 = 0` and `b_3`
  below the row by a factor tending to 0 (`prop:rowslower`); there
  `lambda ~ xi/6`, so the condition of `thm:rowsk` is sharp up to a constant
  factor.  Two lower zeros close this up to the leading constant
  (`thm:rowspair`, `cor:rowsplusone`): a zero of `A_(k-2)` determines the
  coefficient at `y_(k-2)` from the one at `y_(k-1)`, and eliminating it
  leaves at `alpha` the truncation `S_M(alpha)`, of modulus at least
  `lambda`, against `s = |alpha'|/|alpha|` times the next truncation term,
  at most `binom(n+1, 2)(|alpha|/T)**2 ~ 1/2`; so the row `k` holds about
  when `s < 2 lambda`, and `prop:rowslower` has `s/lambda -> 2`.  Hence the
  row `k` holds at `T_a > (n_a + 1) U_(a-1)` once `n_k >= 30` (by hand; the
  margin is positive from `n_k = 26` numerically), and at `n_a + c` for
  every `c > 1/2` once `n_k` is large, while `prop:rowslower` with rational
  `h < 1/2` fails with both separations above `n_a + h`: for large `n_a`
  the additive constant is exactly 1/2 (for the row 2 every `c > 0`).
  Every row and the mass hold at `T_a > sigma(n_a) U_(a-1)`,
  `sigma(n) = n + 1` for `n >= 30` and `min(n + 9, 3 rho_n)` below.  For the
  second row, summing the truncations against the powers of `|alpha|`
  removes `gamma`: `b_2 >= lambda (1 - 1/|alpha|)**2 |f_D| prod |beta|` for
  `|alpha| >= 2` (`prop:rowstwolarge`), while `(x - q)(x + t)**K` has
  `b_2 = lambda prod |beta|`, so the best constant tends to 1 as `|alpha|`
  grows.  Closed for the mass at a fixed separation: every
  multiple with `|f_D| >= 1` has mass at least
  `sum_s s K_s log(T_s/2) - S log 2` once `T_1 > 3` and
  `T_a > 81 U_(a-1)` (`thm:fixedgap`: where one central index falls
  short, two share the charge, one at `T_a/3` and one at `T_a/27`, and
  `lem:tropcount` bounds their shortfalls by `0.82 n_a` and `0.13 n_a`);
  ratios `log(|beta|/6U_(a-1))` at the factor 9 (`cor:annuli` item 2).
  Separation 2 does not suffice: `(x - q)(x + 2q + 1/(2q+1))**2`, `q >= 97`,
  misses the bound by `log(t**2/(128(3q + 2 delta)))`, unbounded in `q`
  (`prop:gaptwo`), and at `q = 97` its separation is `2 + 1/18915`, so
  the least separation exceeds 2.  With few roots above a gap one central
  index suffices once `T_a > 3 rho_(n_a) U_(a-1)`, and `3 rho_n < 81` for
  `n <= 13`: gap by gap, either this or the two positions of
  `thm:fixedgap` give the mass bound (`cor:fewabove`).  For `S = 2` it
  holds at `T_2 > 12 U_1` when `K_2 = 2`, the case of `prop:gaptwo`, and at
  `T_2 > 6 U_1` when `K_2 = 1`, where `(x - q)(x + t)` fails for
  `1 <= t - q < t/32` (separations up to `32/31`).  Below 81 the proof of
  `thm:fixedgap` breaks down where only one vertex above those charged for
  the lower annuli is active in the gap, between tropical roots less than
  `2 log 3` apart, with fewer than `n_a` positions above it; that is how
  `prop:gaptwo` fails (vertices `0, 2, 3`, `f_1 < 1`), and ruling it out
  needs more than the tropical roots, Jensen's formula and the counts of
  `thm:archnewton` and `lem:tropcount`: for `S = 2` a Newton polygon with
  vertices `y_1`, `D - n_2 + 1` and `D` only, tropical roots near `log U_1`
  and just above `log(T_2/2)`, `n_2` large and `K_1` much larger, satisfies
  all of them (at leading order) up to separations near 18.  Numerically
  only: minimizing `Lambda` minus the bound directly over the roots of
  polynomials of degree at most 7 (up to three lower roots, two or three
  upper, up to two others; 60 to 80 restarts each) finds no failure at
  separations 2.05, 2.3, 3 and 5, the least margin about `log 30`; and a
  failure growing with the scale needs coefficients that vanish at leading
  order, which among the lacunary patterns of degree at most 6 without
  other roots reaches separation 2 only for `(x - q)(x + t)**2`, the next
  best being `sqrt 3`.  Numerically only (floating-point vertex enumeration of
  the least mass over real multiples of degree at most `deg P + 1`, about
  150 random root sets per separation, at most three real roots or
  conjugate pairs in the upper annulus), no failure appears at separations 2.2, 3 and 5.  A
  lacunary integer multiple at suitable roots attains `sum_s s K_s log t_s`
  exactly, so the constant 1 is sharp as `min T_s -> oo` and the real cross terms `K_s K_t log t` are false,
  also for pairs near the imaginary axis (`prop:annulisharp`).  Open: the
  least fixed separation for the mass, between `2 + 1/18915` and 81
  (whether 9 suffices; for two annuli with `n_2 <= 8` it is at most 9 by
  `cor:rowstwo`), and whether `T_a > (n_a + 1) U_(a-1)` gives every row
  also where `n_a < 30`, where only `min(n_a + 9, 3 rho_(n_a))` is known
  (`n_a + 9` for `n_a >= 2`, 6 for `n_a = 1`; at `n_a >= 30` it is
  `cor:rowsplusone`).  And the best constant `c` in
  `b_2 >= c lambda (1 - 1/|alpha|) |f_D| prod |beta|` of `thm:rowstwo`
  as `|alpha| -> 1`, between 1/8 and 1 (at least `1 - 1/a_0` over
  `|alpha| >= a_0 >= 2` by `prop:rowstwolarge`).

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
  rays, where `thm:thingauss` gives order `K**2 log R`).  At such coprime
  norms the `p`-adic Newton polygon at each prime `p | n_j` has an edge of
  slope `-v_p(n_j)` ending at some `y_(j,p)`, with `p**(v_p(n_j)(y-i)) | f_i`
  below it; so `Lambda(F)` is at least the sum over `j`, `p` of
  `v_p(n_j) log p` times the distances to `y_(j,p)` of the nonzero positions
  below it, at least `(e_2 - e) log P(0)`, and `A(x^N)` pays `N log P(0)`
  (`prop:gaussadic`).  The valuations alone stay linear in `K`: at `F = P`
  every `y_(j,p) = 1` and the bound is `log P(0)`.  With coefficients of
  modulus at most `V < P(0)` in place of the gap, some multiple has
  `P(0) <= |f_0| <= P(0)**m / V**(m-1)` (Minkowski; `prop:gaussadic`, item
  3), e.g. `|f_0| = 18330 < 65**3` at the norms `5, 13`, `m = 3`, `V = 2`,
  while the sizes alone (`lem:gausscarry` of the complex paper) give only
  `(rho_min/2)**m`.  If
  `rho_min > 2` and `b_2(F) < rho_min/2`, `F = x**e (v + H)` with every
  nonleading coefficient of `H` below `rho_min/2`, so all the roots lie in one
  level set `H(y) = -v` (`prop:gaussheavy`); three Gaussian points above the
  axis share one at every scale: `(y**3 - y)**2 = -(8c**3 + 2c)**2` at
  `+-a + ci`, `2ci` whenever `a**2 - 3c**2 = 1`, with `rho_min = 2c`
  (`+-7 + 4i`, `8i` at `c = 4`).  The level set lies near one circle,
  `rho_min <= rho_j < rho_min Q**(1/deg H)` with
  `Q = (3 rho_min - 2)/(rho_min - 2)`, so `K < 6 rho_min` and
  `Lambda(F) > 2K log(K/12)` (`prop:gausscircle`).  At each prime `p` the
  lowest term `h_l y**l` of `H` bounds the roots (Newton polygon over
  `Q_p`): at most `l` roots of `v + H` have `ord_p > ord_p(h_l)`, all with
  one valuation; as `n_j > 4 h_l**2`, every norm has such a prime, so at
  most `l = ord_0 H` of the `alpha_j` share a norm, `K <= l` when all share
  one (e.g. `deg H >= 8 rho_min**2`), and `h_1 != 0` forces distinct norms
  (`prop:gaussprimes`); `(y**3 + y)**2 = (8c**3 + 2c)**2` at `+-c + ai`
  (Pell `a, c`) attains `K = l = 2` on one norm at every scale, and the
  Pell triples show `K <= l` fails on two norms.  Numerical evidence only:
  exhaustive searches over `H` of degree `5` to `7` (nonleading coefficients
  up to `2` or `3`, points of height up to `60` to `100`), even `H` of degree
  `6` (coefficients up to `6`, height `300`) and even `H` of degree `8`
  (coefficients up to `3`, height `120`) found no level set with four points
  (four need degree `>= 8`), and every one with three came from
  `(y**3 + p y)**2`, `p = -1, 2`, and a Pell equation.  Lattice searches
  (LLL, not exhaustive) for multiples of `P` of degree up to 40, with no
  bound on the coefficients of `H` but `rho_min/2`: symmetric root sets
  `{+-a + ci, ...}` of three points up to height 30 give only those two
  families; symmetric sets of four points up to height 20, and sets of three
  points of one norm `n <= 1000` (degree up to 24), give no multiple with
  middle coefficients below `rho_min/2` (the least ratio found is 3.3, at
  `rho_min**2 = 13`).  Odd quintics `G` for which all five roots of
  `G(y) = iW` are Gaussian (the four-parameter family near a regular
  pentagon, radius up to about 4800) all have a coefficient of `G` far
  above `rho_min`, so `G**2` gives no five-point level set.
  Open: whether `c K**2 log R` holds for all integer multiples at such Gaussian
  roots in a wide sector (the question the introductions of both papers leave),
  whether the number of Gaussian points above the axis in one such level
  set is bounded independently of `rho_min` (the annulus and
  `K <= deg H / 2` alone allow order `rho_min` points when `deg H` is of
  order `rho_min`, so a bound `o(rho_min)` needs more than the positions),
  and whether one norm carries at most two (three need `h_1 = h_2 = 0`).  The case left by separated moduli (`cor:annuli` of the
  complex paper) and common norms (`prop:gausslow`, item 3) is pairwise
  coprime norms in one annulus `[R, 2R]`; there valuations alone give only
  linear bounds (`prop:gaussadic`), and seeded lattice reduction at
  `K = 3..6`, `R = 20, 60`, prime norms, found no multiple cheaper than `P`
  (`2.3` to `2.7` times `K**2 log R`).  A precise step: at odd pairwise coprime norms
  with `gcd(a_j, c_j) = 1`, is there an absolute `C` such that
  `|f_i| < rho_min/2` for `e < i < e + m` forces
  `log |f_e| >= m log P(0) - C m log rho_max`?  With zeros in place of the
  small coefficients this holds with `C = 0` (`prop:gausslow`), and
  `prop:gaussadic`, item 3, shows it is sharp up to `C`; a yes answer makes
  every multiple of `prop:gaussheavy`, item 2, at such norms in one annulus
  pay order `K**2 log R` as `K -> oo`.

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
  at `i = 1`, outside `thm:onepolyrows` and `thm:longdiag`.  The
  hypothesis `nu_2(n) >= nu_1(n)` does not give the identity at `k = 2`
  (Closed, negatively): when `nu_2(n) > nu_1(n)` the position 2 cannot
  break it (by crossing, after `prop:secondrowexact`), but at
  `r = 177/167` exact certificates give `nu_1(50) < nu_2(50) <
  eta_5(50)`, so `V(51,2) <= 1/eta_5(50) = 4.2112... < 1/nu_2(50)`
  (`prop:secondrowhyp`, `tests/test_rows.py`); the margins are below 0.3
  percent, and floating-point experiments find no failure under the
  hypothesis at `r = p/q >= 5/4`, `q <= 20`.
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
  Open: a condition on `r` and `n` that gives the identity at `k = 2`;
  whether the worst finite position or set is always small; whether failures
  occur for every `1 < r < 2`; closed forms, or bounds on the trees, for the
  rows `k >= 3` with `beta_r(n) > 1` -- `thm:finiterows` does not say how to
  find the minimizers `q_N` it branches on, and its thresholds do not
  decrease with `m`.
