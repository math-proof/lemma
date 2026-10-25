/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HolleyFKG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.StrassenFinite.Part2
import Mathlib.Combinatorics.SetFamily.FourFunctions
import Theorem.StatisticalMechanics.Code.Probability.HolleyFKG
open Finset
open scoped NNReal


namespace StatMech

namespace Probability

variable {α : Type*}


section Conditioning

variable [Fintype α] [DecidableEq α] [DistribLattice α]


noncomputable def restrictTo (π : α → ℝ≥0) (S : Finset α) : α → ℝ≥0 :=
  fun a => if a ∈ S then π a else 0


end Conditioning
end Probability
end StatMech
