/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.LinearAlgebra.Lagrange
import Instance.v1.Atlas.ArithmeticGeometry.code.CompleteVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.CompleteVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.RationalLineCriterion
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveComplete
import Def.v1.Atlas.ArithmeticGeometry.code.RationalLineCriterion
import Structure.v1.Atlas.ArithmeticGeometry.code.ProjectiveComplete
import Class.v1.Atlas.ArithmeticGeometry.code.EllipticCurves
universe u


def AlgebraicGeometry.CompletenessValuationCriterion.IsMorphismOfVarieties
    {k : Type u} [Field k]
    (X Y : AlgebraicGeometry.CompletenessValuationCriterion.AlgVariety k)
    (f : X.carrier → Y.carrier) : Prop :=
  ∃ (pullback : Y.functionField →+* X.functionField),


    (∀ a : k, pullback (Y.baseEmbed a) = X.baseEmbed a) ∧


    (∀ (P : X.carrier) (r : Y.functionField),
      r ∈ Y.localRingAt (f P) → pullback r ∈ X.localRingAt P)

