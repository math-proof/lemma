/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.umffullrev.Part2
import Theorem.StatisticalMechanics.Code.Walls.wndwinding.Part3
import Theorem.StatisticalMechanics.Code.Walls.wnuupperhalf.Part5
import Theorem.StatisticalMechanics.Code.Walls.wnaalternate.Part3
import Theorem.StatisticalMechanics.Code.Walls.wcbcolumnbridge.Part4
import Theorem.StatisticalMechanics.Code.Walls.wstsigntoggle.Part2
import Theorem.StatisticalMechanics.Code.Walls.rpccrossflip.Part4
import Def.StatisticalMechanics.Code.Walls.wisindicatorsteps.Part4
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

open StatMech.Walls


theorem wis_indicatorSteps_of_signEqJumps (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wis_SignEqIndicatorJumps z Vc) :
    wst_IndicatorSteps z Vc := by
  obtain ⟨c₀, N, hbase, hperm⟩ := h
  have h01 : ∀ m, wis_indSeq z Vc c₀ m = 0 ∨ wis_indSeq z Vc c₀ m = 1 :=
    fun m => wis_indSeq_in_01 z Vc c₀ m
  have h0 : wis_indSeq z Vc c₀ 0 = 0 := hbase
  rcases hperm with hp | hp
  · obtain ⟨ind, hpm, hind0, hind01, hstep⟩ :=
      wis_nonzeroDiffs_isIndicatorStep (wis_indSeq z Vc c₀) h01 h0 N
    refine ⟨wis_nonzeroDiffs (wis_indSeq z Vc c₀) N, ind, hp, hpm, hind0, Or.inl hind01, hstep⟩
  · obtain ⟨ind, hpm, hind0, hind0neg, hstep⟩ :=
      wis_nonzeroDiffs_neg_isIndicatorStep (wis_indSeq z Vc c₀) h01 h0 N
    refine ⟨wis_nonzeroDiffs (fun i => - wis_indSeq z Vc c₀ i) N, ind, hp, hpm, hind0,
      Or.inr hind0neg, hstep⟩


theorem wis_columnAlternates_of_signEqJumps (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wis_SignEqIndicatorJumps z Vc) :
    wna_ColumnAlternates z Vc :=
  wst_columnAlternates_of_indicatorSteps z Vc (wis_indicatorSteps_of_signEqJumps z Vc h)


theorem wis_unitSquare_rayCount0 :
    jec_rayCount (![0, 1] : Site 2) wwit_unitSquareLoop = 0 := by
  unfold wwit_unitSquareLoop
  simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse,
    jec_rayCount_vsegUp, jec_rayCount_hsegRight, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  norm_num


theorem wis_unitSquare_rayCount1 :
    jec_rayCount (![1, 1] : Site 2) wwit_unitSquareLoop = 1 := by
  unfold wwit_unitSquareLoop
  simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse,
    jec_rayCount_vsegUp, jec_rayCount_hsegRight, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  norm_num


theorem wis_unitSquare_signEqJumps :
    wis_SignEqIndicatorJumps (![1, 1] : Site 2) wwit_unitSquareLoop := by
  have hval0 : wis_indSeq (![1, 1] : Site 2) wwit_unitSquareLoop 0 0 = 0 := by
    show wis_ind (![1, 1] : Site 2) wwit_unitSquareLoop (0 + ((0 : ℕ) : ℤ)) = 0
    unfold wis_ind
    rw [show ((![1, 1] : Site 2) 1) = 1 from by simp, show ((0 : ℤ) + ((0 : ℕ) : ℤ)) = 0 from by simp,
      wis_unitSquare_rayCount0]
    decide
  have hval1 : wis_indSeq (![1, 1] : Site 2) wwit_unitSquareLoop 0 1 = 1 := by
    show wis_ind (![1, 1] : Site 2) wwit_unitSquareLoop (0 + ((1 : ℕ) : ℤ)) = 1
    unfold wis_ind
    rw [show ((![1, 1] : Site 2) 1) = 1 from by simp, show ((0 : ℤ) + ((1 : ℕ) : ℤ)) = 1 from by simp,
      wis_unitSquare_rayCount1]
    decide
  refine ⟨0, 1, hval0, Or.inl ?_⟩
  · 
    rw [wnu_unitSquare_signedList]
    show (wis_nonzeroDiffs (wis_indSeq (![1, 1] : Site 2) wwit_unitSquareLoop 0) 1).Perm [1]
    unfold wis_nonzeroDiffs
    rw [show (List.range 1) = [0] from rfl]
    simp only [List.map_cons, List.map_nil]
    rw [hval1, hval0]
    norm_num


theorem wis_Ltromino_rayCount0 :
    jec_rayCount (![0, 1] : Site 2) wnu_LtrominoLoop = 0 := by
  unfold wnu_LtrominoLoop
  simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse,
    jec_rayCount_vsegUp, jec_rayCount_hsegRight, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  norm_num


theorem wis_Ltromino_rayCount1 :
    jec_rayCount (![1, 1] : Site 2) wnu_LtrominoLoop = 1 := by
  unfold wnu_LtrominoLoop
  simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse,
    jec_rayCount_vsegUp, jec_rayCount_hsegRight, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  norm_num


theorem wis_Ltromino_signEqJumps :
    wis_SignEqIndicatorJumps (![1, 1] : Site 2) wnu_LtrominoLoop := by
  have hval0 : wis_indSeq (![1, 1] : Site 2) wnu_LtrominoLoop 0 0 = 0 := by
    show wis_ind (![1, 1] : Site 2) wnu_LtrominoLoop (0 + ((0 : ℕ) : ℤ)) = 0
    unfold wis_ind
    rw [show ((![1, 1] : Site 2) 1) = 1 from by simp, show ((0 : ℤ) + ((0 : ℕ) : ℤ)) = 0 from by simp,
      wis_Ltromino_rayCount0]
    decide
  have hval1 : wis_indSeq (![1, 1] : Site 2) wnu_LtrominoLoop 0 1 = 1 := by
    show wis_ind (![1, 1] : Site 2) wnu_LtrominoLoop (0 + ((1 : ℕ) : ℤ)) = 1
    unfold wis_ind
    rw [show ((![1, 1] : Site 2) 1) = 1 from by simp, show ((0 : ℤ) + ((1 : ℕ) : ℤ)) = 1 from by simp,
      wis_Ltromino_rayCount1]
    decide
  refine ⟨0, 1, hval0, Or.inr ?_⟩
  · rw [wnu_Ltromino_signedList]
    show (wis_nonzeroDiffs (fun i => - wis_indSeq (![1, 1] : Site 2) wnu_LtrominoLoop 0 i) 1).Perm [-1]
    unfold wis_nonzeroDiffs
    rw [show (List.range 1) = [0] from rfl]
    simp only [List.map_cons, List.map_nil]
    rw [hval1, hval0]
    norm_num


theorem wis_doubleSquare_not_signEqJumps :
    ¬ wis_SignEqIndicatorJumps (![1, 1] : Site 2) wnu_doubleSquare := by
  intro h
  exact wst_doubleSquare_not_indicatorSteps (wis_indicatorSteps_of_signEqJumps _ _ h)


end Lattice
end StatMech
