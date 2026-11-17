module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Algebra.Rat
public import Instance.FieldTheory_RatFuncTower

set_option autoImplicit false

@[expose] public noncomputable section

namespace RatFuncTower

abbrev K0 : Type := FractionRing (Polynomial (AlgebraicClosure ℚ))

end RatFuncTower

end
