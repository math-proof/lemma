module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section31.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
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
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section31
public section
open Topology MulAction CategoryTheory TopologicalSpace

namespace CoveringSpaces

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]

variable {π : Type*} {X : Type*} [Group π] [TopologicalSpace X] [MulAction π X]
  [ContinuousConstSMul π X]

/-- A typeclass asserting that `B` is path connected and *semi-locally simply connected*:
every point has arbitrarily small neighborhoods `V` whose loops at the basepoint become
null-homotopic in `B`. Hypothesis used in the classification of covering spaces. -/
class IsSemiLocallySimplyConnected (B : Type u) [TopologicalSpace B] : Prop where
  pathConnected : PathConnectedSpace B
  semilocal : ∀ (b : B) (U : Set B), U ∈ nhds b →
    ∃ V : Set B, V ∈ nhds b ∧ V ⊆ U ∧
      ∀ (hb : b ∈ V) (γ : Path (⟨b, hb⟩ : V) ⟨b, hb⟩),
        Path.Homotopic (γ.map continuous_subtype_val) (Path.refl b)

end CoveringSpaces
