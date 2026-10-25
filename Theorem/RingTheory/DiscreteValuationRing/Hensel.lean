/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/Hensel.lean -/

import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.LinearCombination


namespace IsDiscreteValuationRing
end IsDiscreteValuationRing
noncomputable section

open Polynomial IsLocalRing Ring

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]

end
