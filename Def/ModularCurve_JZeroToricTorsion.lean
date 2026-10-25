import Mathlib
import Def.ModularCurve_JZeroNeronDataPrime
import Lemma.ModularCurve.ModularUnit

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def jZeroToricTorsion (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (m : ℕ) :
    AddSubgroup (JZero p) :=
  jZeroTorsion p m ⊓ (inertiaInvariantPoints p A).map (nsmulAddMonoidHom (eisensteinNumerator p))

end ModularCurve

end
