import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry

/--
[AlgebraicGeometry_isClosed_of_forall_exists_isOpenImmersion_forall_mem_iff_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isClosed_of_forall_exists_isOpenImmersion_forall_mem_iff_le.lean)
-/
@[main]
private lemma main
  {E : Scheme.{u}}
  {T : Set E}
-- given
  (h : ∀ e : E, ∃ (S : Type u) (_ : CommRing S) (ι : Spec (CommRingCat.of S) ⟶ E) (_ : IsOpenImmersion ι) (I : Ideal S), e ∈ Set.range ι.base ∧ ∀ 𝔮 : PrimeSpectrum S, ι.base 𝔮 ∈ T ↔ I ≤ 𝔮.asIdeal) :
-- imply
  IsClosed T := by
-- proof
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨S, _, ι, _, I, ⟨𝔮ₓ, rfl⟩, hiff⟩ := h x
  refine ⟨ι.base '' (PrimeSpectrum.zeroLocus (I : Set S))ᶜ, ?_, ?_, ?_⟩
  · rintro _ ⟨𝔮, h𝔮, rfl⟩ hT
    exact h𝔮 ((PrimeSpectrum.mem_zeroLocus _ _).mpr (SetLike.coe_subset_coe.mpr ((hiff 𝔮).mp hT)))
  · exact ι.isOpenEmbedding.isOpenMap _ (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
  · exact ⟨𝔮ₓ, fun hz => hx ((hiff 𝔮ₓ).mpr (SetLike.coe_subset_coe.mp ((PrimeSpectrum.mem_zeroLocus _ _).mp hz))), rfl⟩


-- created on 2026-10-05
