/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.Certificate
import CoefficientMass.Chain
import CoefficientMass.ConfDel
import CoefficientMass.Consecutive
import CoefficientMass.Defs
import CoefficientMass.Descartes
import CoefficientMass.Displaced
import CoefficientMass.DisplacedTail
import CoefficientMass.ExpSum
import CoefficientMass.FirstRow
import CoefficientMass.GeomSum
import CoefficientMass.HoleBeta
import CoefficientMass.HoleFill
import CoefficientMass.HoleFree
import CoefficientMass.HoleInt
import CoefficientMass.HoleOne
import CoefficientMass.HoleProd
import CoefficientMass.HoleSum
import CoefficientMass.HoleTwo
import CoefficientMass.Interlace
import CoefficientMass.Interp
import CoefficientMass.Mass
import CoefficientMass.Order
import CoefficientMass.OrderStat
import CoefficientMass.Perturb
import CoefficientMass.RealPart
import CoefficientMass.RowAnnihilate
import CoefficientMass.RowCert
import CoefficientMass.RowDefs
import CoefficientMass.RowStop
import CoefficientMass.Sharp
import CoefficientMass.Signs
import CoefficientMass.Tail
import CoefficientMass.TailBound
import CoefficientMass.TailEq
import CoefficientMass.TailExp
import CoefficientMass.TailJ
import CoefficientMass.TailProd
import CoefficientMass.TailSplit
import CoefficientMass.TailSum
import CoefficientMass.ValsBlock
import CoefficientMass.ValsIdent
import CoefficientMass.ValsMain
import CoefficientMass.ValsMono
import CoefficientMass.ValsSplit
import CoefficientMass.ValsSum
import CoefficientMass.ZeroBound

/-!
# CoefficientMass

The root module, importing the whole library: the statements of
`coefficient-mass.tex` from the zero bound for exponential sums through
Corollary 3.4, the logarithmic mass bound, and from Section 4 Proposition 4.4,
Lemma 4.5 and the reduction of Theorem 4.13 to `(∗_n)`.
-/
