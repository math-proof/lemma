/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.OptionalStopping.Part3
import Theorem.StatisticalMechanics.Code.OSSS.TailSelMP
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


def tsm_switchPiece (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) (k : ℕ) :
    Set (({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ)) :=
  {p | stopVal μ σ f (acp_join t A p.1) = k}


end AdaptDisintegration
end OSSS
end StatMech
