/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Analysis.Normed.Group.Ultra
public import Def.v1.Atlas.ArithmeticGeometry.code.HilbertSymbol
open scoped Classical

public section

variable (F : Type*) [Field F]


namespace hilbertSymbol

variable {F : Type*} [Field F]

/-- $(a, b)_F = 1$ iff the equation $ax^2 + by^2 = 1$ is solvable in $F$. -/
@[simp]
lemma eq_one_iff {a b : Fˣ} :
    hilbertSymbol F a b = 1 ↔ HilbertSymbol.IsSolvable F a b := by
  unfold hilbertSymbol; split_ifs with h <;> simp_all

/-- $(a, b)_F = -1$ iff the equation $ax^2 + by^2 = 1$ is unsolvable in $F$. -/
lemma eq_neg_one_iff {a b : Fˣ} :
    hilbertSymbol F a b = -1 ↔ ¬HilbertSymbol.IsSolvable F a b := by
  unfold hilbertSymbol; split_ifs with h <;> simp_all

end hilbertSymbol
