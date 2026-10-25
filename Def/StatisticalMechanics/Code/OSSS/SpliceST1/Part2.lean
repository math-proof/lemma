/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SpliceST1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.TailSelMPClose.Part2
import Theorem.StatisticalMechanics.Code.OSSS.SpliceST1.Part2
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


noncomputable def sp1_headExtC {n : ℕ} (t : ℕ) (htn : t < n)
    (A : {i : Fin n // (i:ℕ) < t} → ℝ) (c : sp1_Sing n t → ℝ) :
    {i : Fin n // (i:ℕ) < t+1} → ℝ :=
  fun i => if h : (i:ℕ) < t then A ⟨i, h⟩ else c ⟨⟨⟨t, htn⟩, by simp⟩, by simp⟩


end AdaptDisintegration
end OSSS
end StatMech
