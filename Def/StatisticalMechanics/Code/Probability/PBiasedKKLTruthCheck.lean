/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLTruthCheck.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.SummedBKKKLClose
import Theorem.StatisticalMechanics.Code.Probability.PBiasedKKLTruthCheck
open scoped BigOperators
open Finset Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS


def pbkt_AND : ConfigSpace (Fin 2) → Bool := fun ω => ω 0 && ω 1


noncomputable def pbkt_andF : ConfigSpace (Fin 2) → ℝ :=
  fun ω => if pbkt_AND ω then 1 else 0

end StatMech.Probability
