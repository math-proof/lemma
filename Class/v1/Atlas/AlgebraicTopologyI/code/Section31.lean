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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section31
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
