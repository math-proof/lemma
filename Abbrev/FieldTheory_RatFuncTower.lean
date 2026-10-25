import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Algebra.Rat
import Instance.FieldTheory_RatFuncTower

set_option autoImplicit false

noncomputable section

namespace RatFuncTower

abbrev K0 : Type := FractionRing (Polynomial (AlgebraicClosure ℚ))

end RatFuncTower

end
