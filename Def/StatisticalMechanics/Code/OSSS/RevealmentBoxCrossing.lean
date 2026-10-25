/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentBoxCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.RevealmentBoundAssembly
import Theorem.StatisticalMechanics.Code.OSSS.CrossMonotone
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


noncomputable def truncIndC {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    (X : ConfigSpace E) (t : ℕ) : ℝ :=
  if t ≤ stopValC σ f X then (1 : ℝ) else 0


end RevealmentBoxCrossing
end OSSS
end StatMech
