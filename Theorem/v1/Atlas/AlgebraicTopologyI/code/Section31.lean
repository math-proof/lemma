/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section31.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section32
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Lemma32_4
import Def.v1.Atlas.AlgebraicTopologyI.code.Section32.Part2
import Def.v1.Atlas.AlgebraicTopologyI.code.Lemma32_4
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.LocallyConstant.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.Section31.Part2
open Topology MulAction CategoryTheory TopologicalSpace


namespace CoveringSpaces

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]

variable {π : Type*} {X : Type*} [Group π] [TopologicalSpace X] [MulAction π X]
  [ContinuousConstSMul π X]

/-- A morphism of covering spaces over `B'` commutes with path lifting: postcomposing the
lift of a path in `E₁` by the morphism `f : E₁ → E₂` gives the lift of the same path
starting at `f e`. -/
lemma liftPath_comp_covMorphism
    {E₁ : Type u} {E₂ : Type u} {B' : Type u}
    {t₁ : TopologicalSpace E₁} {t₂ : TopologicalSpace E₂} [TopologicalSpace B']
    {p₁ : E₁ → B'} {p₂ : E₂ → B'}
    (cov₁ : @IsCoveringMap _ _ t₁ _ p₁) (cov₂ : @IsCoveringMap _ _ t₂ _ p₂)
    (f : E₁ → E₂) (hf_cont : @Continuous _ _ t₁ t₂ f) (hf_comm : p₂ ∘ f = p₁)
    (γ : C(↑unitInterval, B')) (e : E₁) (he : γ 0 = p₁ e) :
    (@ContinuousMap.mk _ _ t₁ t₂ f hf_cont).comp (cov₁.liftPath γ e he) =
      cov₂.liftPath γ (f e)
        (show γ 0 = p₂ (f e) by rw [he, ← congr_fun hf_comm e]; rfl) := by
  apply (cov₂.eq_liftPath_iff' _).mpr
  refine ⟨?_, ?_⟩
  · ext t
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, Function.comp]
    have h := congr_fun (cov₁.liftPath_lifts γ e he) t
    simp only [Function.comp] at h
    have hc := congr_fun hf_comm (cov₁.liftPath γ e he t)
    simp only [Function.comp] at hc
    rw [hc, h]
  · simp [ContinuousMap.comp_apply, ContinuousMap.coe_mk, cov₁.liftPath_zero]

/-- Equivariance of the fiber map induced by a morphism of covering spaces: the map
`f : E₁ → E₂` intertwines the monodromy actions of `π₁(B', b)` on the fibers
`p₁⁻¹(b)` and `p₂⁻¹(b)`. -/
lemma fiberMap_monodromy_comm
    {E₁ : Type u} {E₂ : Type u} {B' : Type u}
    {t₁ : TopologicalSpace E₁} {t₂ : TopologicalSpace E₂} [TopologicalSpace B']
    {p₁ : E₁ → B'} {p₂ : E₂ → B'}
    (cov₁ : @IsCoveringMap _ _ t₁ _ p₁) (cov₂ : @IsCoveringMap _ _ t₂ _ p₂)
    (f : E₁ → E₂) (hf_cont : @Continuous _ _ t₁ t₂ f) (hf_comm : p₂ ∘ f = p₁)
    {b : B'} (γ : Path.Homotopic.Quotient b b) (e : p₁ ⁻¹' {b}) :
    f (@IsCoveringMap.monodromy _ _ t₁ _ _ cov₁ (x := b) (y := b) γ e).val =
      (@IsCoveringMap.monodromy _ _ t₂ _ _ cov₂ (x := b) (y := b) γ
        ⟨f e.val, by
          have := e.prop
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at this ⊢
          have h := congr_fun hf_comm e.val
          simp only [Function.comp] at h
          rw [h, this]⟩).val := by
  obtain ⟨γ_path, rfl⟩ := Quotient.exists_rep γ
  unfold IsCoveringMap.monodromy
  simp only [Quotient.lift_mk]
  have he_eq : (↑γ_path : C(↑unitInterval, B')) 0 = p₁ e.val := by
    show γ_path 0 = p₁ e.val
    rw [γ_path.source]
    exact (Set.mem_preimage.mp e.prop : p₁ e.val = b).symm
  have key := liftPath_comp_covMorphism cov₁ cov₂ f hf_cont hf_comm (↑γ_path) e.val he_eq
  have h := congr_fun (congrArg DFunLike.coe key) 1
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk] at h
  convert h using 2

end CoveringSpaces
