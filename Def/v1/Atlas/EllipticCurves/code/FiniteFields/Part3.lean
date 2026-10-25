/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Data.Nat.Prime.Basic
import Instance.v1.Atlas.EllipticCurves.code.FiniteFields


section Theorem_3_6

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- Definition 3.17: `f` is separable iff it has `deg f` distinct roots in
any algebraic closure — encoded here via Mathlib's `Polynomial.Separable`. -/
def IsSeparablePoly (f : k[X]) : Prop := f.Separable

/-- A polynomial is inseparable iff it is not separable. -/
def IsInseparablePoly (f : k[X]) : Prop := ¬f.Separable

end Theorem_3_6
