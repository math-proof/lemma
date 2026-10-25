/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveTau
import Def.StatisticalMechanics.Code.OSSS.AdaptMConditional.Part5
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


lemma integrable_truncInd (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) :
    Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => truncInd μ σ f p.1 t)
      ((Vcube n).prod (Vcube n)) :=
  StatMech.Probability.ContinuousFKG.integrable_of_bdd _
    ((measurable_truncInd μ σ f t).comp measurable_fst) (C := 1)
    (fun p => truncInd_le_one μ σ f p.1 t)


end AdaptMConditional
end OSSS
end StatMech
