import Lemma.NarrowRayClassGroup.Main
import Mathlib.RingTheory.DedekindDomain.Different
import Def.NumberField_RayCharacterData

set_option autoImplicit false

noncomputable section

namespace M4aP2

open Real NumberField NumberField.InfinitePlace Deep.NTSupply
open scoped nonZeroDivisors Classical

variable (K : Type) [Field K] [NumberField K]


variable (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)


theorem isParity_one_empty : IsParity K 𝔣 (1 : NarrowRayClassGroup K 𝔣 →* ℂ) ∅ := by
  intro α hα h1
  have hne : ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]
    exact hα
  have hcop : Units.mk0 _ hne ∈ coprimeToModulus K 𝔣 := by
    have h := principalUnit_mem_coprimeToModulus K hα h1
    rw [mem_coprimeToModulus_iff] at h ⊢
    intro v hv
    have := h v hv
    rwa [principalUnit_val] at this
  rw [chiIdeal, dif_pos hne, dif_pos hcop, MonoidHom.one_apply, signAt, Finset.prod_empty]

theorem isPrimitiveMod_top (χ' : NarrowRayClassGroup K ⊤ →* ℂ) : IsPrimitiveMod K ⊤ χ' := by
  intro 𝔣' hle hne
  exact absurd (top_le_iff.mp hle) hne

end M4aP2

end
