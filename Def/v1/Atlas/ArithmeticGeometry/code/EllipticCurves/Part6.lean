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
public import Instance.v1.Atlas.ArithmeticGeometry.code.EllipticCurves.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
universe u

attribute [instance] IsAlgebraicGroup.toIsTopologicalGroup

open WeierstrassCurve


namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (A B : R)

section Theorem_23_16

namespace WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} [DecidableEq F]

namespace WeierstrassCurve

section Theorem26_11

variable {F : Type*} [Field F] {W : WeierstrassCurve F} [W.IsShortNF] [W.IsElliptic]

omit [W.IsElliptic] in
noncomputable def autGroupToFHom
    (_h2 : (2 : F) ≠ 0) (_h3 : (3 : F) ≠ 0) : autGroup F W →* F where
  toFun C := ↑(C : VariableChange F).u
  map_one' := by simp [VariableChange.one_def]
  map_mul' _ _ := by simp [VariableChange.mul_def]

end Theorem26_11
end WeierstrassCurve
end WeierstrassCurve.Affine.Point
end Theorem_23_16
end WeierstrassCurve
