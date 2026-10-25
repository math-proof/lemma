/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part28
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarExtendByIdentityFun_apply_mem
    {Y : Type*} [TopologicalSpace Y] (R : Set Y) (e : R ≃ₜ R)
    {y : Y} (hy : y ∈ R) :
    collarExtendByIdentityFun R e y = (e ⟨y, hy⟩).val := by
  simp [collarExtendByIdentityFun, hy]

theorem collarExtendByIdentityInv_apply_mem
    {Y : Type*} [TopologicalSpace Y] (R : Set Y) (e : R ≃ₜ R)
    {y : Y} (hy : y ∈ R) :
    collarExtendByIdentityInv R e y = (e.symm ⟨y, hy⟩).val := by
  simp [collarExtendByIdentityInv, hy]

theorem collarExtendByIdentity_leftInverse
    {Y : Type*} [TopologicalSpace Y] (R : Set Y) (e : R ≃ₜ R) :
    Function.LeftInverse (collarExtendByIdentityInv R e)
      (collarExtendByIdentityFun R e) := by
  intro y
  by_cases hy : y ∈ R
  · rw [collarExtendByIdentityFun_apply_mem R e hy]
    rw [collarExtendByIdentityInv_apply_mem R e (e ⟨y, hy⟩).property]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨y, hy⟩)
  · simp [collarExtendByIdentityFun, collarExtendByIdentityInv, hy]

theorem collarExtendByIdentity_rightInverse
    {Y : Type*} [TopologicalSpace Y] (R : Set Y) (e : R ≃ₜ R) :
    Function.RightInverse (collarExtendByIdentityInv R e)
      (collarExtendByIdentityFun R e) := by
  intro y
  by_cases hy : y ∈ R
  · rw [collarExtendByIdentityInv_apply_mem R e hy]
    rw [collarExtendByIdentityFun_apply_mem R e (e.symm ⟨y, hy⟩).property]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
  · simp [collarExtendByIdentityFun, collarExtendByIdentityInv, hy]

theorem collarExtendByIdentity_continuous
    {Y : Type*} [TopologicalSpace Y] (R C : Set Y) (e : R ≃ₜ R)
    (hR : IsOpen R) (hC : IsClosed C) (hCR : C ⊆ R)
    (he : ∀ x : R, x.val ∉ C → e x = x) : Continuous (collarExtendByIdentityFun R e) := by
  have hcontR : ContinuousOn (collarExtendByIdentityFun R e) R := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : R.domRestrict (collarExtendByIdentityFun R e) =
        (Subtype.val : R → Y) ∘ e := by
      funext y
      simp [collarExtendByIdentityFun]
    rw [heq]
    exact continuous_subtype_val.comp e.continuous
  have heqC : Set.EqOn (collarExtendByIdentityFun R e) id Cᶜ := by
    intro y hy
    by_cases hyR : y ∈ R
    · rw [collarExtendByIdentityFun_apply_mem R e hyR]
      exact congrArg Subtype.val (he ⟨y, hyR⟩ hy)
    · simp [collarExtendByIdentityFun, hyR]
  have hcontC : ContinuousOn (collarExtendByIdentityFun R e) Cᶜ :=
    continuous_id.continuousOn.congr heqC
  have hunion : R ∪ Cᶜ = Set.univ := by
    apply eq_univ_iff_forall.mpr
    intro y
    by_cases hy : y ∈ C
    · exact Or.inl (hCR hy)
    · exact Or.inr hy
  rw [← continuousOn_univ, ← hunion]
  exact hcontR.union_of_isOpen hcontC hR hC.isOpen_compl

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
