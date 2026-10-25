/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalGluing.Part4
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeInfiniteVolume.Part2
open Filter Set Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

theorem cubicalFixedLoopWilsonSequence_mono
    {beta : Real} (hbeta : 0 ≤ beta) (a b : Nat) :
    Monotone (cubicalFixedLoopWilsonSequence beta a b) := by
  apply monotone_nat_of_le_succ
  intro n
  exact cubicalPaddedWilsonExpectation_mono hbeta a b
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem cubicalFixedLoopWilsonSequence_mem_Icc
    {beta : Real} (hbeta : 0 < beta) (a b n : Nat) :
    cubicalFixedLoopWilsonSequence beta a b n ∈ Set.Icc 0 1 := by
  unfold cubicalFixedLoopWilsonSequence cubicalPaddedWilsonExpectation
  exact gaugeWilsonExpectation_mem_Icc cubicalPlaquetteIncidence
    (fun _ => beta) (fun _ => hbeta) _


end
end StatMech.FrontierA
