import Mathlib
import sympy.Basic
import Structure.v1.Atlas.Buildings.code.Building.Basic.Part2
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments


/--
[delta_injective_in_apt_generic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/StrongIsoExtHelper.lean)
-/
@[path]
lemma delta_injective_in_apt_generic
  [DecidableEq V]
  {b : Building V}
  [Group W]
  {delta : Finset V → Finset V → W}
  {A : SimplicialComplex V}
  {C D₁ D₂ : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hC : A.IsMaximal C)
  (hD₁_mem : D₁ ∈ A.faces)
  (hD₁ : A.IsMaximal D₁)
  (hD₂_mem : D₂ ∈ A.faces)
  (hD₂ : A.IsMaximal D₂)
  (h_delta_compat : ∃ (B_idx : Type) (M : CoxeterMatrix B_idx) (φ : Finset V → M.Group), (∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D) ∧ ∃ (iso : W ≃* M.Group), ∀ C D, C ∈ A.faces → A.IsMaximal C → D ∈ A.faces → A.IsMaximal D → iso (delta C D) = (φ C)⁻¹ * (φ D))
  (h_eq : delta C D₁ = delta C D₂) :
-- imply
  D₁ = D₂ := by
-- proof
  obtain ⟨B_idx, M, φ, hφ_inj, iso, h_compat⟩ := h_delta_compat
  have h1 : iso (delta C D₁) = iso (delta C D₂) := by rw [h_eq]
  rw [h_compat C D₁ hC.1 hC hD₁_mem hD₁,
    h_compat C D₂ hC.1 hC hD₂_mem hD₂] at h1
  have h2 : φ D₁ = φ D₂ := mul_left_cancel h1
  exact hφ_inj D₁ hD₁ D₂ hD₂ h2
-- Any $\delta$-preserving retraction $\bar\rho$ which fixes the apartment
-- agrees on $Y$ with any other $\delta$-preserving partial map $f$.


-- created on 2026-10-24
