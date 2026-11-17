/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanTrueBackbone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
public import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
public import Theorem.StatisticalMechanics.Code.Ising.AizenmanInclusionExclusion.Part3
public import Theorem.StatisticalMechanics.Code.Ising.AizenmanHdom.Part2

public section

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

open StatMech.Sharpness.RandomCurrent


local notation "srcK" => StatMech.Sharpness.RandomCurrent.sources

local notation "compK" => StatMech.Sharpness.RandomCurrent.compOf

end Ising
end StatMech
