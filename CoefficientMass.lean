/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.AllRoots
import CoefficientMass.AllUpper
import CoefficientMass.Certificate
import CoefficientMass.Chain
import CoefficientMass.ConfDel
import CoefficientMass.ConfDelR
import CoefficientMass.ConfPrefix
import CoefficientMass.Consecutive
import CoefficientMass.CrossRows
import CoefficientMass.Crossing
import CoefficientMass.Defs
import CoefficientMass.Descartes
import CoefficientMass.Displaced
import CoefficientMass.DisplacedGen
import CoefficientMass.DisplacedTail
import CoefficientMass.Examples
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
import CoefficientMass.Insert
import CoefficientMass.IntZeros
import CoefficientMass.IntZerosInf
import CoefficientMass.Interlace
import CoefficientMass.Interp
import CoefficientMass.LooseCert
import CoefficientMass.LooseOrder
import CoefficientMass.LooseRatio
import CoefficientMass.LooseRow
import CoefficientMass.Mass
import CoefficientMass.Near
import CoefficientMass.Order
import CoefficientMass.OrderStat
import CoefficientMass.Perturb
import CoefficientMass.PrimeCor
import CoefficientMass.PrimeCount
import CoefficientMass.PrimeLower
import CoefficientMass.PrimeSums
import CoefficientMass.QuadCoef
import CoefficientMass.QuadJensen
import CoefficientMass.QuadMain
import CoefficientMass.QuadMass
import CoefficientMass.QuadRev
import CoefficientMass.QuadRolle
import CoefficientMass.RealPart
import CoefficientMass.RowAnnihilate
import CoefficientMass.RowCert
import CoefficientMass.RowDefs
import CoefficientMass.RowDualLower
import CoefficientMass.RowDualUpper
import CoefficientMass.RowFar
import CoefficientMass.RowFarFactor
import CoefficientMass.RowKth
import CoefficientMass.RowLast
import CoefficientMass.RowOmega
import CoefficientMass.RowPointwise
import CoefficientMass.RowPrefix
import CoefficientMass.RowPrefixRows
import CoefficientMass.RowSep
import CoefficientMass.RowStop
import CoefficientMass.RowTaylor
import CoefficientMass.RowTrunc
import CoefficientMass.RowValue
import CoefficientMass.RowValueDual
import CoefficientMass.Sharp
import CoefficientMass.Signs
import CoefficientMass.Tail
import CoefficientMass.TailBound
import CoefficientMass.TailEq
import CoefficientMass.TailExp
import CoefficientMass.TailGen
import CoefficientMass.TailJ
import CoefficientMass.TailProd
import CoefficientMass.TailSplit
import CoefficientMass.TailSplitGen
import CoefficientMass.TailSum
import CoefficientMass.TruncVertex
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
