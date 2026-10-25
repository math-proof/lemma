/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part30


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

@[simp] theorem fkIsingSquareWiredForwardRingSlotWord_length
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection) :
    (fkIsingSquareWiredForwardRingSlotWord n u d).length =
      (fkIsingSquareWiredBondArcLength n u d).val + 1 := by
  simp [fkIsingSquareWiredForwardRingSlotWord]

theorem fkIsingSquareWiredRingArcContains_active
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d)
    {i : Fin 8}
    (hi : fkIsingSquareWiredRingArcContains n u d i) :
    fkIsingSquareWiredSlotRingActive n (u, i) := by
  classical
  rcases hi with ⟨j, rfl⟩
  have hj := j.isLt
  have hj5 : j.val < 5 := by
    rcases fkIsingSquareWiredBondArcLength_eq_one_or_three_or_five n u d with
        hL | hL | hL <;>
      have hLv := congrArg Fin.val hL <;>
      norm_num at hLv <;>
      omega
  have hjcases : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨
      j.val = 3 ∨ j.val = 4 := by omega
  rcases hjcases with hjv | hjv | hjv | hjv | hjv
  all_goals
    cases d <;>
      by_cases he : fkIsingSquareDirectionAvailable n u .east <;>
      by_cases hnorth : fkIsingSquareDirectionAvailable n u .north <;>
      by_cases hw : fkIsingSquareDirectionAvailable n u .west <;>
      by_cases hs : fkIsingSquareDirectionAvailable n u .south <;>
      simp [fkIsingSquareWiredSlotRingActive,
        fkIsingSquareWiredSlotAvailable,
        fkIsingSquareWiredPortSlotTurn,
        fkIsingSquareWiredPortSlotDirection,
        fkIsingSquareWiredPortSlot,
        fkIsingSquareWiredBondArcLength,
        he, hnorth, hw, hs, hjv] at hd hj ⊢ <;>
      omega

theorem fkIsingSquareWiredForwardRingSlotWord_isChain
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    List.IsChain (fkIsingSquareWiredSlotRingGraph n).Adj
      (fkIsingSquareWiredForwardRingSlotWord n u d) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  simp only [fkIsingSquareWiredForwardRingSlotWord_length] at hi
  simp only [fkIsingSquareWiredForwardRingSlotWord,
    List.getElem_ofFn]
  have hstep :
      (fkIsingSquareWiredPortSlot d .counterclockwise +
          (⟨i, by omega⟩ : Fin 8)) + 1 =
        fkIsingSquareWiredPortSlot d .counterclockwise +
          (⟨i + 1, by omega⟩ : Fin 8) := by
    rw [add_assoc]
    congr 1
    apply Fin.ext
    simp [Fin.add_def]
    omega
  rw [← hstep]
  apply fkIsingSquareWiredSlotRingGraph_adj_succ
  apply fkIsingSquareWiredRingArcContains_active n u d hd
  exact ⟨⟨i, by omega⟩, rfl⟩

theorem fkIsingSquareWiredForwardRingSlotWord_nodup
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection) :
    (fkIsingSquareWiredForwardRingSlotWord n u d).Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro i j hij
  have hi8 : i.val < 8 := by
    have hi := i.isLt
    have hL := (fkIsingSquareWiredBondArcLength n u d).isLt
    simp only [fkIsingSquareWiredForwardRingSlotWord_length] at hi
    omega
  have hj8 : j.val < 8 := by
    have hj := j.isLt
    have hL := (fkIsingSquareWiredBondArcLength n u d).isLt
    simp only [fkIsingSquareWiredForwardRingSlotWord_length] at hj
    omega
  have hslot := congrArg Fin.val (congrArg Prod.snd hij)
  simp only [fkIsingSquareWiredForwardRingSlotWord,
    List.getElem_ofFn] at hslot
  have hoff : (⟨i.val, hi8⟩ : Fin 8) = ⟨j.val, hj8⟩ := by
    apply add_left_cancel
    apply Fin.ext
    exact hslot
  have hv : i.val = j.val := congrArg (@Fin.val 8) hoff
  exact Fin.ext hv

theorem fkIsingSquareWiredForwardRingSlotWord_ne_nil
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection) :
    fkIsingSquareWiredForwardRingSlotWord n u d ≠ [] := by
  intro h
  have hlen := congrArg List.length h
  simp at hlen

theorem fkIsingSquareWiredSlotIntPosition_succ_step
    (n : Nat) (u : (fkSquareBoxPlanar n).V) (i : Fin 8) :
    fkIsingSquareWiredSlotIntPosition n (u, i + 1) =
      fkIsingSquareWiredSlotIntPosition n (u, i) +
        fkIsingSquareWiredUnitDiagonalStep
          (fkIsingSquareWiredRingStepIndex i) := by
  fin_cases i <;>
    simp [fkIsingSquareWiredSlotIntPosition,
      fkIsingSquareWiredPortOctagonOffset,
      fkIsingSquareWiredRingStepIndex,
      fkIsingSquareWiredUnitDiagonalStep, Fin.add_def, Prod.ext_iff] <;>
    omega

theorem fkIsingSquareWiredSlotIntPosition_pred_reverse_step
    (n : Nat) (u : (fkSquareBoxPlanar n).V) (i : Fin 8) :
    fkIsingSquareWiredSlotIntPosition n (u, i) =
      fkIsingSquareWiredSlotIntPosition n (u, i + 1) +
        fkIsingSquareWiredUnitDiagonalStep
          (fkIsingSquareWiredUnitDiagonalReverse
            (fkIsingSquareWiredRingStepIndex i)) := by
  fin_cases i <;>
    simp [fkIsingSquareWiredSlotIntPosition,
      fkIsingSquareWiredPortOctagonOffset,
      fkIsingSquareWiredRingStepIndex,
      fkIsingSquareWiredUnitDiagonalReverse,
      fkIsingSquareWiredUnitDiagonalStep, Fin.add_def, Prod.ext_iff] <;>
    omega


theorem fkIsingSquareWiredSlotRingGraph_exists_path_nextDirection_exact
    (n : Nat) (hn : 0 < n) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    ∃ p : (fkIsingSquareWiredSlotRingGraph n).Walk
        (u, fkIsingSquareWiredPortSlot d .counterclockwise)
        (u, fkIsingSquareWiredPortSlot
          (fkIsingSquareNextDirection n u d) .clockwise),
      p.IsPath ∧
        p.support = fkIsingSquareWiredForwardRingSlotWord n u d := by
  let word := fkIsingSquareWiredForwardRingSlotWord n u d
  have hne : word ≠ [] :=
    fkIsingSquareWiredForwardRingSlotWord_ne_nil n u d
  have hchain : List.IsChain (fkIsingSquareWiredSlotRingGraph n).Adj word :=
    fkIsingSquareWiredForwardRingSlotWord_isChain n u d hd
  let p := SimpleGraph.Walk.ofSupport word hne hchain
  have hsupport : p.support = word :=
    SimpleGraph.Walk.support_ofSupport hne hchain
  have hhead : word.head hne =
      (u, fkIsingSquareWiredPortSlot d .counterclockwise) := by
    simp [word, fkIsingSquareWiredForwardRingSlotWord]
  have hlast : word.getLast hne =
      (u, fkIsingSquareWiredPortSlot
        (fkIsingSquareNextDirection n u d) .clockwise) := by
    have hslot := fkIsingSquareWiredPortSlot_nextDirection n u d
    simp only [word, fkIsingSquareWiredForwardRingSlotWord]
    rw [List.getLast_ofFn_succ]
    exact congrArg (fun slot => (u, slot)) hslot.symm
  let q := p.copy hhead hlast
  refine ⟨q, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def]
    simpa [q, hsupport] using
      fkIsingSquareWiredForwardRingSlotWord_nodup n u d
  · simpa [q, hsupport, word]


end
end StatMech.Universality
