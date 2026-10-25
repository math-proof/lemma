/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentBoxCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.RevealmentBoundAssembly
import Theorem.StatisticalMechanics.Code.OSSS.CrossMonotone
import Def.StatisticalMechanics.Code.OSSS.RevealmentBoxCrossing
open scoped BigOperators
open MeasureTheory


namespace StatMech

namespace OSSS

namespace RevealmentBoxCrossing

open OSSS.Monotonic OSSS.AdaptMConditional StatMech.Probability

open StatMech.OSSS.MonotonicFK

open StatMech.OSSS.AdaptDisintegration

open OSSS.GrandCoupling OSSS.Coding

open StatMech.OSSS.RevealmentBoundAssembly

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma truncInd_eq_truncIndC (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (U : Fin n → ℝ) (t : ℕ) :
    truncInd μ σ f U t = truncIndC σ f (codeMap μ (σ : Fin n → E) U) t := by
  unfold truncInd truncIndC
  rw [stopVal_eq_stopValC]


end RevealmentBoxCrossing
end OSSS
end StatMech
