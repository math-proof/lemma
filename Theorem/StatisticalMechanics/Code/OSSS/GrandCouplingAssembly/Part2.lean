/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.GrandCoupling.Part3
import Theorem.StatisticalMechanics.Code.OSSS.LindebergTree.Part6
import Def.StatisticalMechanics.Code.OSSS.GrandCouplingAssembly
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace GrandCouplingAssembly

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling StatMech.Probability

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma sw_invol (n s : ℕ) : Function.Involutive (sw n s) := by
  intro x
  cases x with
  | inl i => by_cases h : (i:ℕ) < s <;> simp [sw, h]
  | inr i => by_cases h : (i:ℕ) < s <;> simp [sw, h]


end GrandCouplingAssembly
end OSSS
end StatMech
