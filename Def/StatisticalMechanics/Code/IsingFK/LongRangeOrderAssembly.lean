/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/LongRangeOrderAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TwoPointPositiveFull


namespace StatMech

namespace IsingFK

open StatMech.Lattice

variable {d : ℕ}


def HasLongRangeOrder (corr : ℝ → Site d → ℝ) (beta : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x : Site d, c ≤ corr beta x


def HasSpatialDecay (corr : ℝ → Site d → ℝ) (beta : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ n : ℕ, ∀ x : Site d,
    x ∉ box d n → corr beta x < epsilon


end IsingFK
end StatMech
