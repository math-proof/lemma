/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Real.Sqrt
public import Mathlib.GroupTheory.Exponent
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Analysis.Real.Pi.Bounds
public import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.Isogenies
public import Def.v1.Atlas.EllipticCurves.code.PointCounting
@[expose] public section

section Lemma71

variable {R : Type*} [Ring R] (IsInsep : R → Prop)

variable {IsInsep}

/-- The point set $W(F)$ of a Weierstrass curve over a finite field is itself finite,
transported across `pointEquiv` from the (finite) type of optional nonsingular affine
pairs. -/
noncomputable instance pointFintypeInst : Fintype W.Point := by
  classical
  exact Fintype.ofEquiv _ pointEquiv.symm

end Lemma71
