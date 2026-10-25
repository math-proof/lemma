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
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section31
open Topology MulAction CategoryTheory TopologicalSpace


namespace CoveringSpaces

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]

variable {π : Type*} {X : Type*} [Group π] [TopologicalSpace X] [MulAction π X]
  [ContinuousConstSMul π X]

/-- The monodromy action of `π₁(B, b)` on the fiber `p⁻¹(b)`, realised as a group
homomorphism into the endomorphism monoid of the fiber under the monodromy functor. -/
def fiberAction {B : Type u} [TopologicalSpace B] (b : B)
    {E : Type u} [TopologicalSpace E] {p : E → B}
    (cov : IsCoveringMap p) : FundamentalGroup B b →*
    End (cov.monodromyFunctor.obj (FundamentalGroupoid.mk b)) where
  toFun g := cov.monodromyFunctor.map g
  map_one' := cov.monodromyFunctor.map_id _
  map_mul' a c := by
    simp only [End.mul_def]
    exact cov.monodromyFunctor.map_comp c a

/-- The fiber of a covering space over `b` packaged as a `π₁(B, b)`-set via the monodromy
action. -/
def fiberActionObj {B : Type u} [TopologicalSpace B] (b : B)
    (covSpace : CoveringSpaceOver B) : Action (Type u) (FundamentalGroup B b) where
  V := @IsCoveringMap.monodromyFunctor covSpace.E B covSpace.topE _ covSpace.proj
    covSpace.isCoveringMap |>.obj (FundamentalGroupoid.mk b)
  ρ := @fiberAction B _ b covSpace.E covSpace.topE covSpace.proj covSpace.isCoveringMap

end CoveringSpaces
