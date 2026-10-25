/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/woborientbridge.lean -/

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
import Theorem.StatisticalMechanics.Code.Walls.wndwinding.Part3
import Theorem.StatisticalMechanics.Code.Walls.wnuupperhalf.Part5
import Theorem.StatisticalMechanics.Code.Walls.wnaalternate.Part3
import Theorem.StatisticalMechanics.Code.Walls.wcbcolumnbridge.Part4
import Theorem.StatisticalMechanics.Code.Walls.wstsigntoggle.Part2
import Theorem.StatisticalMechanics.Code.Walls.rpccrossflip.Part4
import Theorem.StatisticalMechanics.Code.Walls.wisindicatorsteps.Part5
import Theorem.StatisticalMechanics.Code.Walls.wosorientedsign.Part2
import Theorem.StatisticalMechanics.Code.Walls.welenterleave.Part2
import Def.StatisticalMechanics.Code.Walls.woborientbridge.Part3
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

open StatMech.Walls


theorem wob_orientationConsistent_of_signStepMatchesJump (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wob_SignStepMatchesJump z Vc) :
    wel_OrientationConsistent z Vc :=
  wob_orientationConsistent_of_columnSortedEqJumps z Vc h


theorem wob_canonicalUpDart_signStep (z : Site 2) (c : ℤ) (hc : c ≤ z 0 - 1) :
    wnd_signStep z (![c, z 1 - 1] : Site 2) (![c, z 1] : Site 2) = 1 := by
  unfold wnd_signStep
  rw [if_pos]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp [hc]


theorem wob_canonicalUpDart_signStep_zero (z : Site 2) (c : ℤ) (hc : z 0 - 1 < c) :
    wnd_signStep z (![c, z 1 - 1] : Site 2) (![c, z 1] : Site 2) = 0 := by
  unfold wnd_signStep
  rw [if_neg, if_neg] <;>
    · rintro ⟨⟨_, hle⟩, _⟩; simp only [Matrix.cons_val_zero] at hle; omega


theorem wob_unitSquare_indSeq0 :
    wis_indSeq (![1, 1] : Site 2) wwit_unitSquareLoop 0 0 = 0 := by
  show wis_ind (![1, 1] : Site 2) wwit_unitSquareLoop (0 + ((0 : ℕ) : ℤ)) = 0
  unfold wis_ind
  rw [show ((![1, 1] : Site 2) 1) = 1 from by simp,
    show ((0 : ℤ) + ((0 : ℕ) : ℤ)) = 0 from by simp, wis_unitSquare_rayCount0]
  decide


theorem wob_unitSquare_indSeq1 :
    wis_indSeq (![1, 1] : Site 2) wwit_unitSquareLoop 0 1 = 1 := by
  show wis_ind (![1, 1] : Site 2) wwit_unitSquareLoop (0 + ((1 : ℕ) : ℤ)) = 1
  unfold wis_ind
  rw [show ((![1, 1] : Site 2) 1) = 1 from by simp,
    show ((0 : ℤ) + ((1 : ℕ) : ℤ)) = 1 from by simp, wis_unitSquare_rayCount1]
  decide


theorem wob_unitSquare_columnSortedEqJumps :
    wob_ColumnSortedEqJumps (![1, 1] : Site 2) wwit_unitSquareLoop := by
  refine ⟨0, 1, wob_unitSquare_indSeq0, Or.inl ?_⟩
  rw [wcb_unitSquare_columnSorted]
  
  unfold wis_nonzeroDiffs
  rw [show (List.range 1) = [0] from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [wob_unitSquare_indSeq1, wob_unitSquare_indSeq0]
  norm_num


theorem wob_Ltromino_indSeq0 :
    wis_indSeq (![1, 1] : Site 2) wnu_LtrominoLoop 0 0 = 0 := by
  show wis_ind (![1, 1] : Site 2) wnu_LtrominoLoop (0 + ((0 : ℕ) : ℤ)) = 0
  unfold wis_ind
  rw [show ((![1, 1] : Site 2) 1) = 1 from by simp,
    show ((0 : ℤ) + ((0 : ℕ) : ℤ)) = 0 from by simp, wis_Ltromino_rayCount0]
  decide


theorem wob_Ltromino_indSeq1 :
    wis_indSeq (![1, 1] : Site 2) wnu_LtrominoLoop 0 1 = 1 := by
  show wis_ind (![1, 1] : Site 2) wnu_LtrominoLoop (0 + ((1 : ℕ) : ℤ)) = 1
  unfold wis_ind
  rw [show ((![1, 1] : Site 2) 1) = 1 from by simp,
    show ((0 : ℤ) + ((1 : ℕ) : ℤ)) = 1 from by simp, wis_Ltromino_rayCount1]
  decide


theorem wob_Ltromino_columnSortedEqJumps :
    wob_ColumnSortedEqJumps (![1, 1] : Site 2) wnu_LtrominoLoop := by
  refine ⟨0, 1, wob_Ltromino_indSeq0, Or.inr ?_⟩
  rw [wcb_Ltromino_columnSorted]
  unfold wis_nonzeroDiffs
  rw [show (List.range 1) = [0] from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [wob_Ltromino_indSeq1, wob_Ltromino_indSeq0]
  norm_num


theorem wob_doubleSquare_not_columnSortedEqJumps :
    ¬ wob_ColumnSortedEqJumps (![1, 1] : Site 2) wnu_doubleSquare := by
  intro h
  exact wel_doubleSquare_not_orientationConsistent
    (wob_orientationConsistent_of_columnSortedEqJumps _ _ h)


end Lattice
end StatMech
