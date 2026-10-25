import Mathlib
import Def.ModularCurve_JZeroNeronDataPrime
import Lemma.ModularCurve.ModularUnit
import Def.ModularCurve_JZeroToricTorsion

set_option autoImplicit false

noncomputable section

namespace ModularCurve


theorem mem_jZeroToricTorsion {p : ℕ} [Fact p.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {m : ℕ} {x : JZero p} :
    x ∈ jZeroToricTorsion p A m ↔
      x ∈ jZeroTorsion p m ∧
      ∃ y ∈ inertiaInvariantPoints p A, eisensteinNumerator p • y = x := by
  simp only [jZeroToricTorsion, AddSubgroup.mem_inf, AddSubgroup.mem_map,
    nsmulAddMonoidHom_apply]

end ModularCurve

end
