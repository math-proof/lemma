/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Instance.v1.Atlas.EllipticCurves.code.FiniteFields

@[expose] public section

section Theorem_3_6

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- Definition 3.17: `f` is separable iff it has `deg f` distinct roots in
any algebraic closure — encoded here via Mathlib's `Polynomial.Separable`. -/
def IsSeparablePoly (f : k[X]) : Prop := f.Separable

/-- A polynomial is inseparable iff it is not separable. -/
def IsInseparablePoly (f : k[X]) : Prop := ¬f.Separable

end Theorem_3_6
