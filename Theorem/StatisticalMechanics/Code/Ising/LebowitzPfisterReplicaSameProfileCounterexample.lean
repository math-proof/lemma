/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaSameProfileCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSecondTransfer.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaSameProfileCounterexample
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.RandomCurrent


theorem lpReplicaSameProfileCounter_sources :
    StatMech.Sharpness.RandomCurrent.sources
      lpReplicaSameProfileCounterEnds Finset.univ =
      lpReplicaSameProfileCounterSi ∆
        lpReplicaSameProfileCounterSj ∆
          lpReplicaSameProfileCounterT := by
  decide

theorem lpReplicaSameProfileCounter_ghost_disconn :
    ¬ connK lpReplicaSameProfileCounterEnds Finset.univ 0 1 := by
  intro h
  have hstay : forall x : Fin 8,
      connK lpReplicaSameProfileCounterEnds Finset.univ 0 x ->
        x = 0 ∨ x = 2 := by
    intro x hx
    induction hx with
    | refl => exact Or.inl rfl
    | tail hab hstep ih =>
        rcases hstep with ⟨i, _, ha, hb, hne⟩
        fin_cases i <;>
          simp [lpReplicaSameProfileCounterEnds, Sym2.mem_iff] at ha hb <;>
          aesop
  have := hstay 1 h
  omega


theorem lpReplicaSameProfileCounter_no_target_selector :
    ¬ ((∃ P : Finset (Fin 5), P ⊆ Finset.univ ∧
          StatMech.Sharpness.RandomCurrent.sources
            lpReplicaSameProfileCounterEnds P =
            lpReplicaSameProfileCounterSj ∆ lpReplicaSameProfileCounterT) ∨
        (∃ P : Finset (Fin 5), P ⊆ Finset.univ ∧
          StatMech.Sharpness.RandomCurrent.sources
            lpReplicaSameProfileCounterEnds P =
            lpReplicaSameProfileCounterSi ∆ lpReplicaSameProfileCounterT)) := by
  decide


theorem exists_lpReplica_sameProfile_targetSelector_counterexample :
    ∃ (ends : Fin 5 -> Sym2 (Fin 8))
      (Si Sj T : Finset (Fin 8)),
      StatMech.Sharpness.RandomCurrent.sources ends Finset.univ =
          Si ∆ Sj ∆ T ∧
      ¬ connK ends Finset.univ 0 1 ∧
      ¬ ((∃ P : Finset (Fin 5), P ⊆ Finset.univ ∧
              StatMech.Sharpness.RandomCurrent.sources ends P = Sj ∆ T) ∨
           (∃ P : Finset (Fin 5), P ⊆ Finset.univ ∧
              StatMech.Sharpness.RandomCurrent.sources ends P = Si ∆ T)) := by
  exact ⟨lpReplicaSameProfileCounterEnds,
    lpReplicaSameProfileCounterSi, lpReplicaSameProfileCounterSj,
    lpReplicaSameProfileCounterT, lpReplicaSameProfileCounter_sources,
    lpReplicaSameProfileCounter_ghost_disconn,
    lpReplicaSameProfileCounter_no_target_selector⟩


end StatMech.Ising
