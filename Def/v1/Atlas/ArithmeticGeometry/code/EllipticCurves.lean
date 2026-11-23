/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.GroupTheory.Torsion
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import Mathlib.LinearAlgebra.Lagrange
public import Instance.v1.Atlas.ArithmeticGeometry.code.CompleteVarieties
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.CompleteVarieties
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.RationalLineCriterion
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveComplete
public import Def.v1.Atlas.ArithmeticGeometry.code.RationalLineCriterion
public import Structure.v1.Atlas.ArithmeticGeometry.code.ProjectiveComplete
public import Class.v1.Atlas.ArithmeticGeometry.code.EllipticCurves

@[expose] public section

universe u


def AlgebraicGeometry.CompletenessValuationCriterion.IsMorphismOfVarieties
    {k : Type u} [Field k]
    (X Y : AlgebraicGeometry.CompletenessValuationCriterion.AlgVariety k)
    (f : X.carrier → Y.carrier) : Prop :=
  ∃ (pullback : Y.functionField →+* X.functionField),


    (∀ a : k, pullback (Y.baseEmbed a) = X.baseEmbed a) ∧


    (∀ (P : X.carrier) (r : Y.functionField),
      r ∈ Y.localRingAt (f P) → pullback r ∈ X.localRingAt P)

