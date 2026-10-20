/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Frobenius/Unique.lean -/

import Mathlib.RingTheory.Frobenius

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
  {Q : Ideal S} {σ σ' : G}

namespace IsArithFrobAt

/-- Two arithmetic Frobenius elements at `Q` are equal when the inertia
subgroup of `Q` is trivial. -/
theorem eq_of_inertia_eq_bot (hσ : IsArithFrobAt R σ Q)
    (hσ' : IsArithFrobAt R σ' Q) (hbot : Q.inertia G = ⊥) : σ = σ' := by
  have hmem : σ * σ'⁻¹ ∈ Q.inertia G := hσ.mul_inv_mem_inertia hσ'
  rw [hbot] at hmem
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem)

/-- There is a unique arithmetic Frobenius element at `Q` when the inertia
subgroup of `Q` is trivial. -/
theorem existsUnique_of_inertia_eq_bot [Finite G] [Algebra.IsInvariant R S G]
    [Q.IsPrime] [Finite (S ⧸ Q)] (hbot : Q.inertia G = ⊥) :
    ∃! σ : G, IsArithFrobAt R σ Q := by
  obtain ⟨σ₀, h₀⟩ := exists_of_isInvariant R G Q
  exact ⟨σ₀, h₀, fun σ' h' => eq_of_inertia_eq_bot h' h₀ hbot⟩

end IsArithFrobAt
