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
public import Instance.v1.Atlas.AlgebraicTopologyI.code.Section31
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
