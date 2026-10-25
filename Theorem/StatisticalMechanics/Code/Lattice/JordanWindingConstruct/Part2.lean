/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingConstruct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.WindingColoring.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part10
import Theorem.StatisticalMechanics.Code.Lattice.JordanKeepDual.Part4
import Def.StatisticalMechanics.Code.Lattice.JordanWindingConstruct.Part2
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jwn_cutFlip_bot_iff (a b : Site 2) :
    wcl_cutFlip (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(0:ℤ), -1] a b ↔
      s(a, b) = s(![(0:ℤ), 0], ![(0:ℤ), -1]) := by
  unfold wcl_cutFlip whc_isCross
  simp only [SimpleGraph.edgeSet_bot, Set.mem_empty_iff_false, false_or, or_false]


theorem jwn_squareLoop_cutCount :
    jwn_cutCount (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(0:ℤ), -1] jwn_squareLoop = 1 := by
  classical
  unfold jwn_cutCount
  set flip := wcl_cutFlip (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(0:ℤ), -1] with hflip
  unfold jwn_squareLoop
  rw [wcl_flipCount_cons, wcl_flipCount_cons, wcl_flipCount_cons, wcl_flipCount_cons,
    wcl_flipCount_nil]
  rw [if_pos (Or.inl (by rw [hflip, jwn_cutFlip_bot_iff]))]
  rw [if_neg (by
    rintro (h | h) <;> · rw [hflip, jwn_cutFlip_bot_iff] at h
                         rw [Sym2.eq_iff] at h
                         simp only [site2_eq] at h
                         omega)]
  rw [if_neg (by
    rintro (h | h) <;> · rw [hflip, jwn_cutFlip_bot_iff] at h
                         rw [Sym2.eq_iff] at h
                         simp only [site2_eq] at h
                         omega)]
  rw [if_neg (by
    rintro (h | h) <;> · rw [hflip, jwn_cutFlip_bot_iff] at h
                         rw [Sym2.eq_iff] at h
                         simp only [site2_eq] at h
                         omega)]


theorem jwn_no_cutColoring_bot :
    ¬ ∃ φ : Site 2 → Prop,
      whc_CutColoring (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(0:ℤ), -1] φ := by
  refine jwn_no_cutColoring_of_oddLoop (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(0:ℤ), -1]
    jwn_squareLoop ?_
  rw [jwn_squareLoop_cutCount]; decide


theorem jwn_bot_instance_valid :
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(1:ℤ), 0] ∧
    s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ (⊥ : SimpleGraph (Site 2)).edgeSet ∧
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(![(0:ℤ), 0], ![(1:ℤ), 0]) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  · simp only [SimpleGraph.edgeSet_bot, Set.mem_empty_iff_false, not_false_eq_true]
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  · rw [show (![(0:ℤ), -1] : Site 2) = ![(0:ℤ), 0 - 1] by norm_num, sharedPrimalEdge_bottom]
    unfold faceCorner00 faceCorner10; norm_num


theorem jwn_whitneyColoringResidue_false : ¬ whc_WhitneyColoringResidue := by
  intro hres
  obtain ⟨hpq, hnpq, hfg, hshared⟩ := jwn_bot_instance_valid
  obtain ⟨φ, hcut, _, _⟩ :=
    hres (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(1:ℤ), 0] ![(0:ℤ), 0] ![(0:ℤ), -1]
      hpq hnpq hfg hshared
  exact jwn_no_cutColoring_bot ⟨φ, hcut⟩


theorem jwn_bot_reconnect :
    ((whb_faceRegion (⊥ : SimpleGraph (Site 2))).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] :=
  wcl_faceRegion_bot_reconnect


theorem jwn_cutColoring_of_closedEven (H : SimpleGraph (Site 2)) (f0 g0 : Site 2)
    (hce : wcl_ClosedEven (wcl_cutFlip H f0 g0)) :
    ∃ φ : Site 2 → Prop, whc_CutColoring H f0 g0 φ :=
  ⟨wcl_windingColoring (wcl_cutFlip H f0 g0) f0,
    wcl_windingColoring_isCutColoring H f0 g0 hce f0⟩


theorem jwn_cutColoring_forces_closedEven (H : SimpleGraph (Site 2)) (f0 g0 : Site 2)
    (φ : Site 2 → Prop) (hcut : whc_CutColoring H f0 g0 φ) :
    wcl_ClosedEven (wcl_cutFlip H f0 g0) := by
  intro x w
  exact (jwn_cutColoring_closedEven H f0 g0 φ hcut w).mpr Iff.rfl


end Lattice
end StatMech
