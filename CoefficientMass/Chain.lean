/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import CoefficientMass.Certificate
import CoefficientMass.Mass
import CoefficientMass.OrderStat
import CoefficientMass.RealPart
import CoefficientMass.ZeroBound

/-!
# The Chain to the Logarithmic Mass

This module composes the proved steps of `coefficient-mass.tex`: with the
zero bound proved, Theorem 2.2 alone implies every statement down to
Corollary 3.4.

## Theorems

* `orderStatistics_of_tailBound`.
* `logarithmicMass_of_tailBound`.
-/

namespace CoefficientMass

/-- Theorem 3.2 from Theorem 2.2. -/
theorem orderStatistics_of_tailBound (htb : TailBound) : OrderStatistics :=
  orderStatistics_of_certificate (certificateWithExclusions_of_tailBound zeroBound htb)

/-- Corollary 3.4 from Theorem 2.2. -/
theorem logarithmicMass_of_tailBound (htb : TailBound) : LogarithmicMass :=
  logarithmicMass_of_complexOrderStatistics
    (complexOrderStatistics_of_orderStatistics (orderStatistics_of_tailBound htb))

end CoefficientMass
