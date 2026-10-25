/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Normed.Group.Ultra
import Def.v1.Atlas.ArithmeticGeometry.code.HilbertSymbol
open scoped Classical

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
