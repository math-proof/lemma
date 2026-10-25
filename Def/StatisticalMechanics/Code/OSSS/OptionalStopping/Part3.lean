/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/OptionalStopping.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.TailCondLawClose.Part3
import Theorem.StatisticalMechanics.Code.OSSS.OptionalStopping.Part2
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


noncomputable def osp_fill {n : ℕ} (t s k : ℕ)
    (q : ((({i : Fin n // (i : ℕ) < t} → ℝ) × ({i : Fin n // ¬ (i : ℕ) < t} → ℝ))
            × (Fin n → ℝ))) : Fin n → ℝ :=
  adaptWt (acp_join t q.1.1 q.1.2) q.2 k s


end AdaptDisintegration
end OSSS
end StatMech
