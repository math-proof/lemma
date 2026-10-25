/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.VarGapProve2
import Theorem.StatisticalMechanics.Code.Probability.PBiasedTwoPoint.Part3
import Theorem.StatisticalMechanics.Code.Probability.MasterFamilyProve.Part2
open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def mfp_masterFamily (q : ℝ) : Prop := frh_openResidue q


end StatMech.Probability
