/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/StrassenFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.StrassenFull.Part7
import Theorem.StatisticalMechanics.Code.Probability.StrassenFinite
open Finset
open scoped NNReal


namespace StatMech

namespace Probability

variable {P : Type*}


section Hard

open Transport

variable [Fintype P] [DecidableEq P] [PartialOrder P]
  [DecidableRel ((· ≤ ·) : P → P → Prop)]


noncomputable def piOfVec (c : OrderPairs P → ℝ) : P × P → NNReal :=
  fun p => if h : p.1 ≤ p.2 then (c ⟨p, h⟩).toNNReal else 0

end Hard
end Probability
end StatMech
