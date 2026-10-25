/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CurrentWeight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Ising.AizenmanInclusionExclusion.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanTrueBackbone.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanHdom.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def acwRestrict (p : Sym2 V → Prop) [DecidablePred p] (n : Current V) : Current V :=
  fun e => if p e then n e else 0


def acwInternal (S : Finset V) (e : Sym2 V) : Prop := ∀ z ∈ e, z ∈ S

end Ising
end StatMech
