/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusPairSourceBoxCurrent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoundarySourceLaw.Part4
import Theorem.StatisticalMechanics.Code.FrontierB.PairSourceBoxCurrent.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
import Def.StatisticalMechanics.Code.FrontierB.PlusPairSourceBoxCurrent
open MeasureTheory
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Lattice

open StatMech.IsingFK


theorem boxSiteSucc_interior {d n : ℕ}
    (x : StatMech.FK.boxVerts d n) :
    boxSiteSucc x ∈ boxCurrentInterior d (n + 1) := by
  have hnot : ¬ StatMech.FK.boxBoundary d (n + 1) (boxSiteSucc x) := by
    rw [hbx_boxBoundary_succ_iff]
    exact not_not_intro x.2
  simp [boxCurrentInterior, hnot]

theorem boxSiteSucc_ne {d n : ℕ}
    {x y : StatMech.FK.boxVerts d n} (hxy : x ≠ y) :
    boxSiteSucc x ≠ boxSiteSucc y := by
  intro h
  apply hxy
  apply Subtype.ext
  exact congrArg (fun z => z.1) h

theorem pair_boxSiteSucc_inter_interior {d n : ℕ}
    (x y : StatMech.FK.boxVerts d n) :
    ({boxSiteSucc x, boxSiteSucc y} :
        Finset (StatMech.FK.boxVerts d (n + 1))) ∩
        boxCurrentInterior d (n + 1) =
      {boxSiteSucc x, boxSiteSucc y} := by
  apply Finset.inter_eq_left.mpr
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact boxSiteSucc_interior x
  · exact boxSiteSucc_interior y


theorem plusPairBoundarySourceCurrentSum_pos
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) (hxy : x ≠ y) :
    0 < boundarySourceCurrentSum (StatMech.FK.boxGraph d (n + 1)) beta
      (fun _ => 1) (boxCurrentInterior d (n + 1))
      {boxSiteSucc x, boxSiteSucc y} := by
  apply boundarySourceCurrentSum_pos_of_currentSum_pos
    (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1)
    hbeta.le (fun _ => by positivity)
    (boxCurrentInterior d (n + 1)) {boxSiteSucc x, boxSiteSucc y}
    {boxSiteSucc x, boxSiteSucc y}
  · exact pair_boxSiteSucc_inter_interior x y
  · exact boxCurrentSum_pair_pos d (n + 1) beta hbeta
      (boxSiteSucc x) (boxSiteSucc y) (boxSiteSucc_ne hxy)


end StatMech.FrontierB
