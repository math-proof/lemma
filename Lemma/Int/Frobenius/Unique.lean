import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.RingTheory.Frobenius.Unique
open IsArithFrobAt


namespace IsArithFrobAt

/--
[eq_of_inertia_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Frobenius/Unique.lean)
-/
@[path]
lemma eq_of_inertia_eq_bot
  [CommRing R] [CommRing S] [Algebra R S] [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
  {Q : Ideal S}
  {σ σ' : G}
-- given
  (hσ : IsArithFrobAt R σ Q)
  (hσ' : IsArithFrobAt R σ' Q)
  (hbot : Q.inertia G = ⊥) :
-- imply
  σ = σ' := by
-- proof
  have hmem : σ * σ'⁻¹ ∈ Q.inertia G := hσ.mul_inv_mem_inertia hσ'
  rw [hbot] at hmem
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem)

end IsArithFrobAt

namespace IsArithFrobAt

/--
[existsUnique_of_inertia_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Frobenius/Unique.lean)
-/
@[path]
lemma existsUnique_of_inertia_eq_bot
  [CommRing R] [CommRing S] [Algebra R S] [Group G] [MulSemiringAction G S] [SMulCommClass G R S] [Finite G] [Algebra.IsInvariant R S G]
  {Q : Ideal S} [Q.IsPrime] [Finite (S ⧸ Q)]
  {σ σ' : G}
-- given
  (hbot : Q.inertia G = ⊥) :
-- imply
  ∃! σ : G, IsArithFrobAt R σ Q := by
-- proof
  obtain ⟨σ₀, h₀⟩ := exists_of_isInvariant R G Q
  exact ⟨σ₀, h₀, fun σ' h' => eq_of_inertia_eq_bot h' h₀ hbot⟩

end IsArithFrobAt


-- created on 2026-10-20
-- updated on 2026-10-26
