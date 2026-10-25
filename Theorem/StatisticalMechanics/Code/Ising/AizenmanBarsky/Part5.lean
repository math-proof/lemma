/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanBarsky.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.GHSFull.Part3
import Def.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem bondEnergy_le_ghsSum (β h : ℝ) (o : V) (hghs : GHSThreePointSym G β h o) :
    bondEnergySusceptibility G β h o ≤ ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e := by
  unfold bondEnergySusceptibility
  exact Finset.sum_le_sum hghs


theorem aizenman_barsky_inequality (β h : ℝ) (o : V) (J : ℝ)
    (hghs : GHSThreePointSym G β h o)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
  calc bondEnergySusceptibility G β h o
      ≤ ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e := bondEnergy_le_ghsSum G β h o hghs
    _ = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := hfactor

end Ising
end StatMech
