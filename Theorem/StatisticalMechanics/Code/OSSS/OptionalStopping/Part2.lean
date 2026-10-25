/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OptionalStopping.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.TailCondLawClose.Part3
import Def.StatisticalMechanics.Code.OSSS.OptionalStopping.Part2
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000


namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly

open StatMech.Probability OSSS.AdaptiveTau OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma osp_proj_meas {n : ℕ} (t : ℕ) : Measurable (osp_proj (n := n) t) :=
  (measurable_snd.comp measurable_fst).prodMk measurable_snd


lemma osp_proj_measurePreserving {n : ℕ} (t : ℕ) :
    MeasurePreserving (osp_proj (n := n) t)
      (((ubfHead n t).prod (ubfTail n t)).prod (Vcube n))
      ((ubfTail n t).prod (Vcube n)) := by
  unfold osp_proj
  have h1 : MeasurePreserving (Prod.snd : (({i : Fin n // (i : ℕ) < t} → ℝ) × ({i : Fin n // ¬ (i : ℕ) < t} → ℝ)) → _)
      ((ubfHead n t).prod (ubfTail n t)) (ubfTail n t) := measurePreserving_snd
  exact (h1.prod (MeasurePreserving.id (Vcube n)))


end AdaptDisintegration
end OSSS
end StatMech
