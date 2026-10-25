/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Nodup
import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Structure.v1.Atlas.TheoryOfComputation.code.Tableau


namespace NPCompleteness

/--
Syntax of propositional Boolean formulas over variables indexed by ℕ.
A `BoolFormula` is built from variables, the constants `true` and `false`,
and the connectives ¬, ∧, ∨.
-/
inductive BoolFormula : Type where
  | var : ℕ → BoolFormula
  | trueConst : BoolFormula
  | falseConst : BoolFormula
  | not : BoolFormula → BoolFormula
  | and : BoolFormula → BoolFormula → BoolFormula
  | or : BoolFormula → BoolFormula → BoolFormula
  deriving DecidableEq, Repr

end NPCompleteness
