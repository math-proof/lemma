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
