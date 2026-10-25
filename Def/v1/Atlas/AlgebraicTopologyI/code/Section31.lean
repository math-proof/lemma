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
open Topology MulAction CategoryTheory TopologicalSpace


namespace CoveringSpaces

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]

/-- (Definition 31.1) A continuous map `p : E → B` is a *covering space* if every point
preimage is discrete and every `b ∈ B` has a neighborhood `V` so that `p⁻¹(V)` splits
homeomorphically as `V × p⁻¹(b)` over `V`. Defined here as `IsCoveringMap p`. -/
def IsCoveringSpace (p : E → B) : Prop :=
  IsCoveringMap p

/-- (Definition 31.3) The action of a group `π` on a space `X` is *principal*
(equivalently, totally discontinuous) if every `x` has a neighborhood `U` such that
`gU ∩ U ≠ ∅` forces `g = 1`. -/
def IsPrincipalAction (π : Type*) (X : Type*) [Group π] [TopologicalSpace X]
    [MulAction π X] : Prop :=
  ∀ x : X, ∃ U ∈ 𝓝 x, ∀ g : π, ((g • ·) '' U ∩ U).Nonempty → g = 1

end CoveringSpaces
