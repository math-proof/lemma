/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.WindingColoring.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Instance.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part3
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jeb_square_closedContour : jce_ClosedContour (imageGraph jbc_Pce).edgeSet := by
  classical
  intro v
  rw [jce_degree, Finset.card_filter, Fin.sum_univ_four]
  simp only [jce_nbr, whc_square_mem_iff, Sym2.eq_iff, whc_site_eq_iff, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  set x := v 0; set y := v 1
  by_cases hx0 : x = 0 <;> by_cases hx1 : x = 1 <;> by_cases hy0 : y = 0 <;> by_cases hy1 : y = 1 <;>
    (simp_all; try omega)


theorem jeb_Htest_insert_eq :
    insert (s(![(0:ℤ), 0], ![1, 0])) whc_Htest.edgeSet = (imageGraph jbc_Pce).edgeSet := by
  classical
  have hbot : s(![(0:ℤ), 0], ![1, 0]) ∈ (imageGraph jbc_Pce).edgeSet := by
    rw [whc_square_mem_iff]; tauto
  ext e
  rw [Set.mem_insert_iff, whc_Htest_mem]
  constructor
  · rintro (rfl | ⟨hsq, _⟩)
    · exact hbot
    · exact hsq
  · intro h
    by_cases hb : e = s(![(0:ℤ), 0], ![1, 0])
    · left; exact hb
    · right; exact ⟨h, hb⟩


theorem jeb_unitSquare_biconditional_fires :
    (whc_Htest.Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] ↔
      ¬ ((whb_faceRegion whc_Htest).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable
        ![(0:ℤ), 0] ![(0:ℤ), -1]) := by
  have hpq : (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(1:ℤ), 0] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  have hnpq : s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ whc_Htest.edgeSet := by
    rw [whc_Htest_mem]; push Not; intro _; rw [Sym2.eq_iff]; simp only [whc_site_eq_iff]; norm_num
  have hfg : (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  have hshared : sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(![(0:ℤ), 0], ![(1:ℤ), 0]) := by
    rw [show (![(0:ℤ), -1] : Site 2) = ![(0:ℤ), 0 - 1] by norm_num, sharedPrimalEdge_bottom]
    unfold faceCorner00 faceCorner10; norm_num
  have hcc : jce_ClosedContour
      ((insert (sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1]) whc_Htest.edgeSet.toFinset
        : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2))) := by
    classical
    rw [Finset.coe_insert, Set.coe_toFinset, hshared, jeb_Htest_insert_eq]
    exact jeb_square_closedContour
  exact jeb_correctWhitney_of_evenDegree whc_Htest jeb_Htest_le
    ![(0:ℤ), 0] ![(1:ℤ), 0] ![(0:ℤ), 0] ![(0:ℤ), -1] hpq hnpq hfg hshared hcc

end Lattice
end StatMech
