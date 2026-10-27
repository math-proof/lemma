import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false


universe u

/--
[image_connectedComponentIn_subset_diff_of_forall_mem_irreducibleComponents_image_ne](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_image_connectedComponentIn_subset_diff_of_forall_mem_irreducibleComponents_image_ne.lean)
-/
@[path]
private lemma main
  {X : Type u} [TopologicalSpace X] (Z₁ Z₂ : Set X)
  (hZ₁c : IsClosed Z₁) (hZ₂c : IsClosed Z₂) (hZ₁ : IsIrreducible Z₁) (hZ₂ : IsIrreducible Z₂)
  (hcov : Z₁ ∪ Z₂ = Set.univ) (h₁₂ : ¬ Z₁ ⊆ Z₂) (h₂₁ : ¬ Z₂ ⊆ Z₁)
  (τ : Homeomorph X X) (hτ : ∀ Z ∈ irreducibleComponents X, τ '' Z ≠ Z)
  (U : Set X) (hτU : τ '' U = U) (p : X)
  (hU₁ : Z₁ ∩ U = connectedComponentIn U p) (hU₂ : Z₂ ∩ U = U \ connectedComponentIn U p) :
  -- imply
  ∀ y ∈ connectedComponentIn U p, τ y ∈ U \ connectedComponentIn U p := by
  -- proof
  classical
  have dich : ∀ T : Set X, IsIrreducible T → T ⊆ Z₁ ∨ T ⊆ Z₂ := fun T hT =>
    isPreirreducible_iff_isClosed_union_isClosed.mp hT.isPreirreducible Z₁ Z₂ hZ₁c hZ₂c
      (Set.subset_univ _)
  have hZ₁m : Z₁ ∈ irreducibleComponents X := by
    refine ⟨hZ₁, fun T hT hle =>
      Or.elim (dich T hT) id (fun h => False.elim (absurd (Set.Subset.trans hle h) h₁₂))⟩
  have himg : ∀ Z ∈ irreducibleComponents X, τ '' Z ∈ irreducibleComponents X := by
    intro Z hZ
    refine ⟨hZ.1.image τ τ.continuous.continuousOn, fun T hT hle => ?_⟩
    have h1 : Z ⊆ τ.symm '' T := by
      intro z hz
      refine ⟨τ z, hle ⟨z, hz, rfl⟩, τ.symm_apply_apply z⟩
    have h2 : τ.symm '' T ⊆ Z := hZ.2 (hT.image τ.symm τ.symm.continuous.continuousOn) h1
    intro t ht
    refine ⟨τ.symm t, h2 ⟨t, ht, rfl⟩, τ.apply_symm_apply t⟩
  have hτZ₁ : τ '' Z₁ ⊆ Z₂ :=
    Or.elim (dich (τ '' Z₁) (hZ₁.image τ τ.continuous.continuousOn))
      (fun h => False.elim (hτ Z₁ hZ₁m (Set.Subset.antisymm h ((himg Z₁ hZ₁m).2 hZ₁ h))))
      id
  intro y hy
  have hy₁ : y ∈ Z₁ ∩ U := by
    rw [hU₁]
    refine hy
  have hτy : τ y ∈ Z₂ ∩ U :=
    ⟨hτZ₁ ⟨y, hy₁.1, rfl⟩, hτU ▸ ⟨y, hy₁.2, rfl⟩⟩
  rw [hU₂] at hτy
  refine hτy


-- created on 2026-10-20
