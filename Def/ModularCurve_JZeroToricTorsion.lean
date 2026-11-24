module
public import Mathlib
public import Def.ModularCurve_JZeroNeronDataPrime
public import Theorem.HahnSeries.ModularUnit
set_option autoImplicit false


public section

noncomputable section

namespace ModularCurve

def jZeroToricTorsion (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (m : ℕ) :
    AddSubgroup (JZero p) :=
  jZeroTorsion p m ⊓ (inertiaInvariantPoints p A).map (nsmulAddMonoidHom (eisensteinNumerator p))

end ModularCurve

end
