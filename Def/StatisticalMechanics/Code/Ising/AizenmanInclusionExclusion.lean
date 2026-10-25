/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanInclusionExclusion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanInclusionExclusion
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

namespace RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


def aie_allConn (ends : ι → Sym2 V) (m : Finset ι) (o x y : V) : Prop :=
  connK ends m x y ∧ connK ends m o y ∧ connK ends m o x


def aie_noneConn (ends : ι → Sym2 V) (m : Finset ι) (o x y : V) : Prop :=
  ¬ connK ends m x y ∧ ¬ connK ends m o y ∧ ¬ connK ends m o x


end RandomCurrent
end Sharpness
end StatMech
