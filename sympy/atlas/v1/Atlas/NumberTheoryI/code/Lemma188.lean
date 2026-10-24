/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lemma188.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.NumberTheoryI.code.ArithmeticFunctions
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.ArithmeticFunctions
import Mathlib.FieldTheory.Finite.Basic

open scoped Classical
open ArithmeticFunction

def ArithFunc.IsDirichletCharModulus (f : ArithFunc) (m : ℕ) : Prop :=
  f.IsTotallyMultiplicative ∧ ArithFunc.IsPeriodic f m ∧ ∀ n : ℕ, f n ≠ 0 ↔ Nat.Coprime m n
