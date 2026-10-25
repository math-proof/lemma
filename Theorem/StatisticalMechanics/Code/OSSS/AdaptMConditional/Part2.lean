/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveTau
import Def.StatisticalMechanics.Code.OSSS.AdaptMConditional.Part2
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace AdaptMConditional

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly

open StatMech.Probability OSSS.LindebergTree OSSS.AdaptiveTau

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma detAtC_card {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (X : ConfigSpace E) :
    detAtC (σ : Fin n → E) f X n := by
  intro w hw
  have hall : ∀ e, w e = X e := by
    intro e; exact hw e (by rw [prefixSet_card σ]; exact Finset.mem_univ e)
  rw [funext hall]


end AdaptMConditional
end OSSS
end StatMech
