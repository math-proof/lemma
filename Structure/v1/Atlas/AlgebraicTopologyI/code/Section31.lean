/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section31.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
public import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
public import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section32
public import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Lemma32_4
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
public import Class.v1.Atlas.AlgebraicTopologyI.code.Section31
public section

open Topology MulAction CategoryTheory TopologicalSpace


namespace CoveringSpaces

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]

variable {π : Type*} {X : Type*} [Group π] [TopologicalSpace X] [MulAction π X]
  [ContinuousConstSMul π X]

/-- The data of a covering space over a fixed base `B`: a total space `E` together with
its topology, a continuous projection `proj : E → B`, and a proof that `proj` is a
covering map. -/
structure CoveringSpaceOver (B : Type u) [TopologicalSpace B] where
  E : Type u
  topE : TopologicalSpace E
  proj : E → B
  continuous_proj : @Continuous E B topE _ proj
  isCoveringMap : @IsCoveringMap E B topE _ proj

/-- A morphism of covering spaces over `B`: a continuous map between the total spaces
that commutes with the projections. -/
structure CoveringSpaceOver.Hom {B : Type u} [TopologicalSpace B]
    (E₁ E₂ : CoveringSpaceOver B) where
  toFun : E₁.E → E₂.E
  continuous_toFun : @Continuous E₁.E E₂.E E₁.topE E₂.topE toFun
  proj_comm : E₂.proj ∘ toFun = E₁.proj

end CoveringSpaces
