/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeProve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.MasterFamilyProve2.Part2
import Theorem.StatisticalMechanics.Code.Probability.CoupledTensorizeProve
open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS


def ctp_OR : ConfigSpace (Fin 2) → Bool := fun ω => ω 0 || ω 1


noncomputable def ctp_f : ConfigSpace (Fin 2) → ℝ := fun ω => if ctp_OR ω then (1 : ℝ) else 0

end StatMech.Probability
