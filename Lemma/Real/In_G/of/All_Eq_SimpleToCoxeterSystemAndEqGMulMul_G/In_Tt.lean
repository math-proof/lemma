import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.BNPair.Generalized.Theorems
open GeneralizedBNPair


namespace GeneralizedBNPair

/--
[trivial_action_in_G](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/Generalized/Theorems.lean)
-/
@[path]
private lemma trivial_action_in_G
  [Fintype B_idx]
  [DecidableEq B_idx]
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {gbp : GeneralizedBNPair Gt M}
  {t : Gt}
-- given
  (ht : t ∈ gbp.Tt)
  (htrivial : ∀ (s : B_idx) (n : gbp.strictBNPair.N), gbp.strictBNPair.π n = M.toCoxeterSystem.simple s → ∃ (n' : gbp.strictBNPair.N), gbp.strictBNPair.π n' = M.toCoxeterSystem.simple s ∧ ((n' : gbp.G) : Gt) = t * ((n : gbp.G) : Gt) * t⁻¹) :
-- imply
  t ∈ gbp.G :=
-- proof
  gbp.building_uniqueness_lemma t (gbp.Tt_le_Bt ht) htrivial

end GeneralizedBNPair

namespace GeneralizedBNPair

/--
[Tt_perm_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/Generalized/Theorems.lean)
-/
@[path]
private lemma Tt_perm_injective
  [Fintype B_idx]
  [DecidableEq B_idx]
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {gbp : GeneralizedBNPair Gt M}
  [Fintype B_idx]
  [DecidableEq B_idx]
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {gbp : GeneralizedBNPair Gt M}
  {t₁ t₂ : Gt}
-- given
  (ht₁ : t₁ ∈ gbp.Tt)
  (ht₂ : t₂ ∈ gbp.Tt)
  (hsame : ∀ (s : B_idx) (n : gbp.strictBNPair.N), gbp.strictBNPair.π n = M.toCoxeterSystem.simple s → ∃ (n₁' n₂' : gbp.strictBNPair.N), gbp.strictBNPair.π n₁' = gbp.strictBNPair.π n₂' ∧ ((n₁' : gbp.G) : Gt) = t₁ * ((n : gbp.G) : Gt) * t₁⁻¹ ∧ ((n₂' : gbp.G) : Gt) = t₂ * ((n : gbp.G) : Gt) * t₂⁻¹) :
-- imply
  t₁⁻¹ * t₂ ∈ gbp.G := by
-- proof
  have ht12 : t₁⁻¹ * t₂ ∈ gbp.Tt := gbp.Tt.mul_mem (gbp.Tt.inv_mem ht₁) ht₂
  have ht1inv : t₁⁻¹ ∈ gbp.Tt := gbp.Tt.inv_mem ht₁
  obtain ⟨σ₁, hσ₁⟩ := gbp.Tt_stabilizes_S t₁ ht₁
  obtain ⟨σ₂, hσ₂⟩ := gbp.Tt_stabilizes_S t₂ ht₂
  obtain ⟨τ, hτ⟩ := gbp.Tt_stabilizes_S t₁⁻¹ ht1inv
  have hσ_eq : σ₁ = σ₂ := by
    ext s
    obtain ⟨n₀, hn₀⟩ := gbp.strictBNPair.π_surj (M.toCoxeterSystem.simple s)
    obtain ⟨m₁, hm₁_π, hm₁_conj⟩ := hσ₁ s n₀ hn₀
    obtain ⟨m₂, hm₂_π, hm₂_conj⟩ := hσ₂ s n₀ hn₀
    obtain ⟨n₁', n₂', hπ_eq, hn₁'_conj, hn₂'_conj⟩ := hsame s n₀ hn₀
    have hm₁_eq_n₁' : m₁ = n₁' := by
      have : ((m₁ : gbp.G) : Gt) = ((n₁' : gbp.G) : Gt) := by
        rw [hm₁_conj, hn₁'_conj]
      exact Subtype.val_injective (Subtype.val_injective this)
    have hm₂_eq_n₂' : m₂ = n₂' := by
      have : ((m₂ : gbp.G) : Gt) = ((n₂' : gbp.G) : Gt) := by
        rw [hm₂_conj, hn₂'_conj]
      exact Subtype.val_injective (Subtype.val_injective this)
    have : gbp.strictBNPair.π m₁ = gbp.strictBNPair.π m₂ := by
      rw [hm₁_eq_n₁', hm₂_eq_n₂']; exact hπ_eq
    rw [hm₁_π, hm₂_π] at this
    exact CoxeterSystem.simple_injective M.toCoxeterSystem this
  have hτσ : ∀ s, τ (σ₁ s) = s := by
    intro s
    obtain ⟨n₀, hn₀⟩ := gbp.strictBNPair.π_surj (M.toCoxeterSystem.simple s)
    obtain ⟨m₁, hm₁_π, hm₁_conj⟩ := hσ₁ s n₀ hn₀
    obtain ⟨m₃, hm₃_π, hm₃_conj⟩ := hτ (σ₁ s) m₁ hm₁_π
    have hm₃_eq_n₀ : ((m₃ : gbp.G) : Gt) = ((n₀ : gbp.G) : Gt) := by
      rw [hm₃_conj, hm₁_conj]
      group
    have : m₃ = n₀ := Subtype.val_injective (Subtype.val_injective hm₃_eq_n₀)
    rw [this, hn₀] at hm₃_π
    exact (CoxeterSystem.simple_injective M.toCoxeterSystem hm₃_π).symm
  apply trivial_action_in_G gbp (t₁⁻¹ * t₂) ht12
  intro s n hn
  obtain ⟨n₂', hn₂'_π, hn₂'_conj⟩ := hσ₂ s n hn
  obtain ⟨n₃, hn₃_π, hn₃_conj⟩ := hτ (σ₂ s) n₂' hn₂'_π
  refine ⟨n₃, ?_, ?_⟩
  ·
    rw [hn₃_π, ← hσ_eq, hτσ]
  ·
    rw [hn₃_conj, hn₂'_conj]
    group

end GeneralizedBNPair

namespace GeneralizedBNPair

/--
[Tlifted_le_Blifted](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/Generalized/Theorems.lean)
-/
@[path]
private lemma Tlifted_le_Blifted
  [Fintype B_idx]
  [DecidableEq B_idx]
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {gbp : GeneralizedBNPair Gt M} :
-- imply
  gbp.Tlifted ≤ gbp.Blifted := by
-- proof
  unfold Tlifted Blifted
  exact Subgroup.map_mono (gbp.strictBNPair.T_eq ▸ inf_le_left)

end GeneralizedBNPair

namespace GeneralizedBNPair

/--
[Tlifted_le_Nlifted](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/Generalized/Theorems.lean)
-/
@[path]
private lemma Tlifted_le_Nlifted
  [Fintype B_idx]
  [DecidableEq B_idx]
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {gbp : GeneralizedBNPair Gt M} :
-- imply
  gbp.Tlifted ≤ gbp.Nlifted := by
-- proof
  unfold Tlifted Nlifted
  exact Subgroup.map_mono (gbp.strictBNPair.T_eq ▸ inf_le_right)

end GeneralizedBNPair

namespace GeneralizedBNPair

/--
[T_le_Tt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/Generalized/Theorems.lean)
-/
@[path]
private lemma T_le_Tt
  [Fintype B_idx]
  [DecidableEq B_idx]
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {gbp : GeneralizedBNPair Gt M} :
-- imply
  gbp.Tlifted ≤ gbp.Tt := by
-- proof
  rwa [gbp.Tt_eq]
    (le_trans gbp.Tlifted_le_Blifted gbp.B_le_Bt)
    (le_trans gbp.Tlifted_le_Nlifted gbp.N_le_Nt)

end GeneralizedBNPair


-- created on 2026-10-23
-- updated on 2026-10-24
