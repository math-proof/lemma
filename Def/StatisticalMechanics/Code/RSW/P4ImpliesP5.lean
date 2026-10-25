/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/P4ImpliesP5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.ExpDecayUpgrade
import Theorem.StatisticalMechanics.Code.RSW.P5Equivalences.Part2
open Real Filter


namespace StatMech

namespace RSW

namespace P4ImpliesP5

open StatMech.RSW.Box


def rp4_StretchedExpDecay (a : ℕ → ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∀ n, a n ≤ Real.exp (-(((n : ℝ)) ^ α))


def rp4_ExpDecay (a : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ n, a n ≤ C * Real.exp (-c * n)


def rp4_P4 (a : ℕ → ℝ) : Prop := ¬ rp4_ExpDecay a


end P4ImpliesP5
end RSW
end StatMech
