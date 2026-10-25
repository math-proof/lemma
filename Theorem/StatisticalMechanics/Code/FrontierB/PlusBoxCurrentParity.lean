/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusBoxCurrentParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.BoundaryCurrentParity.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part6
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
import Def.StatisticalMechanics.Code.FrontierB.PlusBoxCurrentParity
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice

open StatMech.IsingFK

theorem extendInteriorPlus_configEquiv_symm
    (d n : ℕ) (tau : ConfigSpace (StatMech.FK.boxVerts d n))
    (v : StatMech.FK.boxVerts d (n + 1)) :
    extendInteriorPlus (boxCurrentInterior d (n + 1))
        ((boxCurrentInteriorConfigEquiv d n).symm tau) v =
      if h : v.1 ∈ box d n then tau ⟨v.1, h⟩ else true := by
  by_cases hv : v.1 ∈ box d n
  · rw [dif_pos hv]
    have hvnot : ¬ StatMech.FK.boxBoundary d (n + 1) v := by
      rw [hbx_boxBoundary_succ_iff]
      exact not_not_intro hv
    have hvint : v ∈ boxCurrentInterior d (n + 1) := by
      simp [boxCurrentInterior, hvnot]
    rw [extendInteriorPlus]
    simp only [dif_pos hvint]
    change tau (boxCurrentInteriorEquiv d n ⟨v, hvint⟩) = tau ⟨v.1, hv⟩
    congr 1
  · rw [dif_neg hv]
    have hvbd : StatMech.FK.boxBoundary d (n + 1) v :=
      (hbx_boxBoundary_succ_iff d n v).2 hv
    apply extendInteriorPlus_outside
    simp [boxCurrentInterior, hvbd]

theorem extendInteriorPlus_configEquiv_symm_eq_glue
    (d n : ℕ) (tau : ConfigSpace (StatMech.FK.boxVerts d n))
    (v : StatMech.FK.boxVerts d (n + 1)) :
    extendInteriorPlus (boxCurrentInterior d (n + 1))
        ((boxCurrentInteriorConfigEquiv d n).symm tau) v =
      glue (plusField d) tau v.1 := by
  rw [extendInteriorPlus_configEquiv_symm]
  by_cases hv : v.1 ∈ box d n
  · rw [dif_pos hv, glue_mem]
  · rw [dif_neg hv, glue_not_mem _ _ hv]
    rfl

end StatMech.FrontierB
