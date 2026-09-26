import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Flow
import sympy.dynamics.actor_critic
import sympy.Basic
import Lemma.OmegaLimit.In_OmegaLimit.is.All_In_Closure_Image2_Ici
import Lemma.ContinuousSemiflow.IsForwardInvariant
open Filter


@[main]
private lemma main
  {α : Type*} [TopologicalSpace α] [T2Space α]
  {Φ : ContinuousSemiflow α}
  {K : Set α}
-- given
  (h₀ : IsCompact K)
  (h₁ : IsForwardInvariant Φ.toFun K) :
-- imply
  Φ.Invariant (omegaLimit atTop Φ.toFun K) := by
-- proof
  intro t ht
  apply Set.Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact ContinuousSemiflow.IsForwardInvariant Φ K ht hy
  intro y hy
  let tail : ℝ → Set α := fun T => closure (Set.image2 Φ.toFun (Set.Ici T) K)
  have htail : ∀ T, 0 ≤ T → tail T ⊆ K := fun T hT =>
    closure_minimal (Set.image2_subset_iff.2 fun s hs x hx => h₁ (hT.trans hs) hx) h₀.isClosed
  have hcpt : ∀ T, 0 ≤ T → IsCompact (tail T) := fun T hT => h₀.of_isClosed_subset isClosed_closure (htail T hT)
  have hmono : ∀ T T', T ≤ T' → tail T' ⊆ tail T := fun T T' h =>
    closure_mono (Set.image2_subset_right (Set.Ici_subset_Ici.2 h))
  let F : Set.Ici (0 : ℝ) → Set α := fun T => tail T ∩ Φ.toFun t ⁻¹' {y}
  have hclosed : ∀ T : Set.Ici (0 : ℝ), IsClosed (F T) := fun T =>
    isClosed_closure.inter (isClosed_singleton.preimage (Φ.continuous_apply t ht))
  have hne : ∀ T : Set.Ici (0 : ℝ), (F T).Nonempty := by
    intro T
    have hT : (0 : ℝ) ≤ T := T.2
    have hsub : tail (T + t) ⊆ Φ.toFun t '' tail T := by
      refine closure_minimal ?_ ((hcpt T hT).image (Φ.continuous_apply t ht)).isClosed
      rintro _ ⟨s, hs, x, hx, rfl⟩
      simp only [Set.mem_Ici] at hs
      refine ⟨Φ.toFun (s - t) x, subset_closure ⟨s - t, by simp only [Set.mem_Ici]; linarith, x, hx, rfl⟩, ?_⟩
      rw [← Φ.map_add' t (s - t) ht (by linarith) x, add_sub_cancel]
    obtain ⟨z, hz, hzy⟩ := hsub ((OmegaLimit.In_OmegaLimit.is.All_In_Closure_Image2_Ici Φ.toFun K y).1 hy (T + t))
    exact ⟨z, hz, hzy⟩
  have hdir : Directed (· ⊇ ·) F := by
    intro T₁ T₂
    refine ⟨⟨max T₁ T₂, Set.mem_Ici.2 (le_max_of_le_left (Set.mem_Ici.1 T₁.2))⟩, ?_, ?_⟩
    · exact Set.inter_subset_inter_left _ (hmono _ _ (le_max_left _ _))
    · exact Set.inter_subset_inter_left _ (hmono _ _ (le_max_right _ _))
  have : Nonempty (Set.Ici (0 : ℝ)) := ⟨⟨0, Set.mem_Ici.2 le_rfl⟩⟩
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed F hdir hne
    (fun T => (hcpt T T.2).inter_right (isClosed_singleton.preimage (Φ.continuous_apply t ht))) hclosed
  rw [Set.mem_iInter] at hz
  refine ⟨z, (OmegaLimit.In_OmegaLimit.is.All_In_Closure_Image2_Ici Φ.toFun K z).2 fun T => hmono T (max T 0) (le_max_left _ _) (hz ⟨max T 0, Set.mem_Ici.2 (le_max_right _ _)⟩).1, (hz ⟨0, Set.mem_Ici.2 le_rfl⟩).2⟩


-- created on 2026-09-26
