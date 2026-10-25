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
import Theorem.v1.Atlas.TheoryOfComputation.code.NPCompleteness.Part2


namespace CookLevin

open TuringMachine NPCompleteness

/-- The "free-max-var" function: alias of `maxVarSucc` used in coincidence lemmas.
Returns one more than the largest variable index appearing in `φ`. -/
def fmv : BoolFormula → ℕ
  | .var n => n + 1 | .trueConst | .falseConst => 0
  | .not φ => fmv φ | .and φ ψ | .or φ ψ => max (fmv φ) (fmv ψ)

end CookLevin
