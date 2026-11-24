module
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section32
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Lemma32_4
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section32.Part2
public import Def.v1.Atlas.AlgebraicTopologyI.code.Lemma32_4
public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.RepresentationTheory.Rep.Iso
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.LocallyConstant.Basic
public import Structure.v1.Atlas.AlgebraicTopologyI.code.Section31
open Topology MulAction CategoryTheory TopologicalSpace


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section31.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace CoveringSpaces

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]

variable {π : Type*} {X : Type*} [Group π] [TopologicalSpace X] [MulAction π X]
  [ContinuousConstSMul π X]

/-- The category `Cov_B` of covering spaces over `B`, with morphisms given by
projection-preserving continuous maps. -/
instance coveringSpaceOverCategory {B : Type u} [TopologicalSpace B] :
    Category (CoveringSpaceOver B) where
  Hom := CoveringSpaceOver.Hom
  id E := {
    toFun := id
    continuous_toFun := @continuous_id E.E E.topE
    proj_comm := rfl
  }
  comp {X Y Z} f g := {
    toFun := g.toFun ∘ f.toFun
    continuous_toFun := @Continuous.comp X.E Y.E Z.E X.topE Y.topE Z.topE
      (f := f.toFun) (g := g.toFun) g.continuous_toFun f.continuous_toFun
    proj_comm := by
      ext x
      have h1 := congr_fun g.proj_comm (f.toFun x)
      have h2 := congr_fun f.proj_comm x
      simp only [Function.comp] at h1 h2 ⊢
      rw [h1, h2]
  }

end CoveringSpaces
