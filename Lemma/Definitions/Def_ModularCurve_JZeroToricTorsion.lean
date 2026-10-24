import Mathlib
import Lemma.Definitions.Def_ModularCurve_JZeroNeronDataPrime
import Lemma.Definitions.Def_ModularCurve_ModularUnit

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def jZeroToricTorsion (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (m : ℕ) :
    AddSubgroup (JZero p) :=
  jZeroTorsion p m ⊓ (inertiaInvariantPoints p A).map (nsmulAddMonoidHom (eisensteinNumerator p))

theorem mem_jZeroToricTorsion {p : ℕ} [Fact p.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {m : ℕ} {x : JZero p} :
    x ∈ jZeroToricTorsion p A m ↔
      x ∈ jZeroTorsion p m ∧
      ∃ y ∈ inertiaInvariantPoints p A, eisensteinNumerator p • y = x := by
  simp only [jZeroToricTorsion, AddSubgroup.mem_inf, AddSubgroup.mem_map,
    nsmulAddMonoidHom_apply]

end ModularCurve

end
