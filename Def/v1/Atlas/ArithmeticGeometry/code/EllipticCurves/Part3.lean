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
public import Abbrev.v1.Atlas.ArithmeticGeometry.code.EllipticCurves.Part3

@[expose] public section

universe u

attribute [instance] IsAlgebraicGroup.toIsTopologicalGroup

open WeierstrassCurve


namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (A B : R)

section Theorem_23_16

namespace WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} [DecidableEq F]

def MazurCyclicOrders : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12}

def MazurProductOrders : Finset ℕ := {1, 2, 3, 4}

namespace WeierstrassCurve.Affine.Point

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} [DecidableEq F]

def lineThirdIntersection : W.Point → W.Point → W.Point
  | zero, Q => -Q
  | some x₁ y₁ h₁, zero => -(some x₁ y₁ h₁)
  | some x₁ y₁ h₁, some x₂ y₂ h₂ =>
      if hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂ then 0
      else some _ _ (nonsingular_negAdd h₁ h₂ hxy)

end WeierstrassCurve.Affine.Point
end WeierstrassCurve.Affine.Point
end Theorem_23_16
end WeierstrassCurve
