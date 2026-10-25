/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataRepairCounterexampleHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRowDataRepairRelation.Part4


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

theorem weightedCollision_not_conn_zero_three_any
    (K : Finset (Fin 4)) :
    ¬ connK weightedCollisionEnds K 0 3 := by
  intro h
  exact not_connK_of_no_incident (u := (3 : Fin 4)) (v := 0)
    (by decide) (fun i _ => by
      fin_cases i <;> simp [weightedCollisionEnds])
    (connK_symm weightedCollisionEnds K h)


theorem weightedCollision_leaf_color_two
    (c : leftFiber weightedCollisionEnds Finset.univ {1, 0} {0, 2} 0 3) :
    c.1 ⟨3, Finset.mem_univ 3⟩ = 2 := by
  have hsrc := c.2.2.2.1
  have hmem : (2 : Fin 4) ∈
      sources weightedCollisionEnds (colorClass Finset.univ c.1 2) := by
    rw [hsrc]
    simp
  rw [mem_sources] at hmem
  rcases hmem with ⟨n, hn⟩
  have hne : degK weightedCollisionEnds
      (colorClass Finset.univ c.1 2) 2 ≠ 0 := by omega
  unfold degK at hne
  rcases Finset.card_ne_zero.mp hne with ⟨i, hi⟩
  rw [Finset.mem_filter] at hi
  have hi3 : i = 3 := by
    fin_cases i <;> simp [weightedCollisionEnds] at hi ⊢
  subst i
  rw [mem_colorClass_iff] at hi
  exact hi.1.2

theorem weightedCollision_leaf_subset_middle
    (c : leftFiber weightedCollisionEnds Finset.univ {1, 0} {0, 2} 0 3) :
    ({3} : Finset (Fin 4)) ⊆ middleMask Finset.univ c.1 := by
  intro i hi
  have hi3 : i = 3 := by simpa using hi
  subst i
  rw [middleMask, Finset.mem_union]
  right
  rw [mem_colorClass_iff]
  exact ⟨Finset.mem_univ 3, weightedCollision_leaf_color_two c⟩

theorem weightedCollision_leaf_swap_right
    (c : leftFiber weightedCollisionEnds Finset.univ {1, 0} {0, 2} 0 3) :
    RightPattern weightedCollisionEnds Finset.univ {1, 0} {0, 2} 0 3
      (balancedSwap Finset.univ {3} ∅ c.1) := by
  apply rightPattern_of_balancedTransfer c.2
  · exact weightedCollision_leaf_subset_middle c
  · exact Finset.empty_subset _
  · decide
  · simp [sources, degK]
  · unfold RowsDisconnect
    exact ⟨weightedCollision_not_conn_zero_three_any _,
      weightedCollision_not_conn_zero_three_any _⟩


end StatMech.GrahamGHS.FourColor
