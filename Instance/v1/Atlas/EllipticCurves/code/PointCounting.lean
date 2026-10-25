/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.Exponent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Real.Pi.Bounds
import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Isogenies
import Def.v1.Atlas.EllipticCurves.code.PointCounting


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
