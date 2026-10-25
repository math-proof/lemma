/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Coding.Part6
import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
import Theorem.StatisticalMechanics.Code.Probability.ContinuousFKG.Part3
import Theorem.StatisticalMechanics.Code.OSSS.GrandCoupling.Part2
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace GrandCoupling

open OSSS.Monotonic OSSS.Coding StatMech.Probability

variable {E : Type*} [Fintype E] [DecidableEq E]


def Wt {n : ℕ} (U V : Fin n → ℝ) (s : ℕ) : Fin n → ℝ :=
  fun i => if (i : ℕ) < s then V i else U i


end GrandCoupling
end OSSS
end StatMech
