/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.BdEdgeMatchStarHull
import Def.StatisticalMechanics.Code.Lattice.WindingColoring.Part6
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem wcl_correctColoringResidue_holds : wcl_CorrectColoringResidue := by
  intro H f0 g0 hfg hce
  refine ⟨wcl_windingColoring (wcl_cutFlip H f0 g0) f0,
    wcl_windingColoring_isCutColoring H f0 g0 hce f0, ?_,
    wcl_deleted_separated_of_closedEven H hfg hce⟩
  set φ := wcl_windingColoring (wcl_cutFlip H f0 g0) f0
  have := (wcl_windingColoring_isCutColoring H f0 g0 hce f0) f0 g0 hfg
  have hmark : whc_isCross H f0 g0 ∨ s(f0, g0) = s(f0, g0) := Or.inr rfl
  rw [this] at hmark
  tauto


theorem wcl_witness_closedEven :
    wcl_ClosedEven (wcl_cutFlip whc_Htest ![(0:ℤ), 0] ![(0:ℤ), -1]) :=
  (wcl_exists_cutColoring_iff_closedEven whc_Htest ![(0:ℤ), 0] ![(0:ℤ), -1]).mp
    ⟨whc_phiWitness, whc_cutColoring_witness⟩


theorem wcl_witness_residue_fires :
    ∃ φ : Site 2 → Prop, whc_CutColoring whc_Htest ![(0:ℤ), 0] ![(0:ℤ), -1] φ ∧
      ¬ (φ ![(0:ℤ), 0] ↔ φ ![(0:ℤ), -1]) ∧
      ¬ ((whb_faceRegion whc_Htest).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable
        ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  have hfg : (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  exact wcl_correctColoringResidue_holds whc_Htest ![(0:ℤ), 0] ![(0:ℤ), -1] hfg
    wcl_witness_closedEven


theorem wcl_whitney_forward_of_closedEven (H : SimpleGraph (Site 2)) (p q f0 g0 : Site 2)
    (_hpq : (hypercubicLattice 2).Adj p q) (_hnpq : s(p, q) ∉ H.edgeSet)
    (hfg : (hypercubicLattice 2).Adj f0 g0) (_hshared : sharedPrimalEdge f0 g0 = s(p, q))
    (hce : wcl_ClosedEven (wcl_cutFlip H f0 g0)) :
    ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 :=
  wcl_deleted_separated_of_closedEven H hfg hce

end Lattice
end StatMech
