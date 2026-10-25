/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaAggregateSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOffdiagSwitching.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaAggregateSwitching
open Finset
open scoped BigOperators symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaMatchingDisconnTwoOffDiag_eq_sum_toggledMass
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (beta : Real) (J : Sym2 (LPReplicaCurrentVertex V) -> Real) :
    lpMatchingDisconnTwoOffDiag (lpReplicaCurrentGraph G sites) beta J
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 =
      ∑ i : I, ∑ j : I,
        lpReplicaOffdiagToggledMass G sites hsite beta J i j := by
  unfold lpMatchingDisconnTwoOffDiag
  dsimp only
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · rw [if_pos hij]
    simp [lpReplicaOffdiagToggledMass, hij]
  · rw [if_neg hij]
    rw [lpReplica_sourcePairDisconnSum_offdiag_eq_sum_toggled
      G sites hsite hij beta J]
    simp only [lpReplicaOffdiagToggledMass, hij, dite_false]


theorem lpReplicaMatchingDisconnTwo_eq_sum_toggledMass
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (beta : Real) (J : Sym2 (LPReplicaCurrentVertex V) -> Real) :
    lpMatchingDisconnTwo (lpReplicaCurrentGraph G sites) beta J
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 =
      ∑ i : I, ∑ j : I,
        lpReplicaOffdiagToggledMass G sites hsite beta J i j := by
  rw [lpMatchingDisconnTwo_eq_offDiag
    (lpReplicaCurrentGraph G sites) beta J
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1]
  · exact lpReplicaMatchingDisconnTwoOffDiag_eq_sum_toggledMass
      G sites hsite beta J
  · simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1]

end
end StatMech.Ising
