/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectedMatchingCut
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterFiveCurrentPairing
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.GhostCurrentRep

noncomputable section

variable {W : Type*} [DecidableEq W]


theorem lpFiveToggle12_orbitAB
    (Si Sj T : Finset W) :
    lpFiveToggle12 T (lpFiveOrbitABPos Si Sj T) =
      lpFiveOrbitABNeg Si Sj T := by
  apply LPFiveSourceAllocation.ext <;>
    simp only [lpFiveToggle12, lpFiveOrbitABPos, lpFiveOrbitABNeg]
  all_goals
    ext x
    simp only [Finset.mem_symmDiff, Finset.notMem_empty]
    tauto


theorem lpFiveToggle12_involutive (T : Finset W) :
    Function.Involutive (lpFiveToggle12 T) := by
  intro a
  apply LPFiveSourceAllocation.ext <;> simp [lpFiveToggle12]

theorem lpFiveToggle14_involutive (T : Finset W) :
    Function.Involutive (lpFiveToggle14 T) := by
  intro a
  apply LPFiveSourceAllocation.ext <;> simp [lpFiveToggle14]

theorem lpFiveToggle23_involutive (T : Finset W) :
    Function.Involutive (lpFiveToggle23 T) := by
  intro a
  apply LPFiveSourceAllocation.ext <;> simp [lpFiveToggle23]


theorem lpFiveToggle12_total (T : Finset W)
    (a : LPFiveSourceAllocation W) :
    (lpFiveToggle12 T a).total = a.total := by
  change (a.source1 ∆ T ∆ (a.source2 ∆ T) ∆ a.source3 ∆
      a.source4 ∆ a.source5) =
    a.source1 ∆ a.source2 ∆ a.source3 ∆ a.source4 ∆ a.source5
  calc
    _ = (a.source1 ∆ a.source2 ∆ a.source3 ∆ a.source4 ∆
        a.source5) ∆ T ∆ T := by ac_rfl
    _ = _ := symmDiff_symmDiff_cancel_right _ _

theorem lpFiveToggle14_total (T : Finset W)
    (a : LPFiveSourceAllocation W) :
    (lpFiveToggle14 T a).total = a.total := by
  change (a.source1 ∆ T ∆ a.source2 ∆ a.source3 ∆
      (a.source4 ∆ T) ∆ a.source5) =
    a.source1 ∆ a.source2 ∆ a.source3 ∆ a.source4 ∆ a.source5
  calc
    _ = (a.source1 ∆ a.source2 ∆ a.source3 ∆ a.source4 ∆
        a.source5) ∆ T ∆ T := by ac_rfl
    _ = _ := symmDiff_symmDiff_cancel_right _ _

theorem lpFiveToggle23_total (T : Finset W)
    (a : LPFiveSourceAllocation W) :
    (lpFiveToggle23 T a).total = a.total := by
  change (a.source1 ∆ (a.source2 ∆ T) ∆ (a.source3 ∆ T) ∆
      a.source4 ∆ a.source5) =
    a.source1 ∆ a.source2 ∆ a.source3 ∆ a.source4 ∆ a.source5
  calc
    _ = (a.source1 ∆ a.source2 ∆ a.source3 ∆ a.source4 ∆
        a.source5) ∆ T ∆ T := by ac_rfl
    _ = _ := symmDiff_symmDiff_cancel_right _ _


end
end StatMech.Ising
