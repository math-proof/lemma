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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section31
open Topology MulAction CategoryTheory TopologicalSpace


namespace CoveringSpaces

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]

variable {π : Type*} {X : Type*} [Group π] [TopologicalSpace X] [MulAction π X]
  [ContinuousConstSMul π X]

/-- The "take the fiber at `b`" functor `Cov_B → π₁(B, b)-Set` sending a covering space
to its fiber equipped with the monodromy action, and a morphism to its restriction
between fibers. -/
def fiberFunctor {B : Type u} [TopologicalSpace B] (b : B) :
    CoveringSpaceOver B ⥤ Action (Type u) (FundamentalGroup B b) where
  obj := fiberActionObj b
  map {E₁ E₂} f :=
    { hom := fun e =>
        ⟨f.toFun e.val, by
          have := e.prop
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at this ⊢
          have h := congr_fun f.proj_comm e.val
          simp only [Function.comp] at h
          rw [h, this]⟩
      comm := fun g => by
        ext ⟨e, he⟩
        apply Subtype.ext
        simp only [types_comp_apply, fiberActionObj, fiberAction]
        exact fiberMap_monodromy_comm E₁.isCoveringMap E₂.isCoveringMap
          f.toFun f.continuous_toFun f.proj_comm g ⟨e, he⟩ }
  map_id X := by
    apply Action.Hom.ext
    funext ⟨e, he⟩
    apply Subtype.ext
    rfl
  map_comp {X Y Z} f g := by
    apply Action.Hom.ext
    funext ⟨e, he⟩
    apply Subtype.ext
    rfl


end CoveringSpaces
