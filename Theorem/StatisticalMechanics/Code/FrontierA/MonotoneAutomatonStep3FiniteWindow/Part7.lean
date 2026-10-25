/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonAbsorptionReduction.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteEventMultivalued
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3FiniteWindow.Part6
open MeasureTheory Set Finset SimpleGraph
open scoped ENNReal NNReal BigOperators


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


theorem mem_shiftedBoxFinset_of_l1dist_le {z x : Site d} {D : ℕ}
    (h : l1dist d z x ≤ D) : x ∈ shiftedBoxFinset z D := by
  classical
  rw [shiftedBoxFinset, Finset.mem_image]
  refine ⟨x - z, ?_, by simp⟩
  rw [mem_boxFinsetBK_iff]
  intro k
  have hterm : (z k - x k).natAbs ≤ l1dist d z x := by
    unfold l1dist
    exact Finset.single_le_sum
      (f := fun j : Fin d => (z j - x j).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have habs : (x k - z k).natAbs = (z k - x k).natAbs := by
    rw [← Int.natAbs_neg]
    congr 1
    ring
  simpa [Pi.sub_apply, habs] using hterm.trans h

theorem shiftedBoxFinset_card_le (z : Site d) (D : ℕ) :
    (shiftedBoxFinset z D).card ≤ (boxFinsetBK d D).card := by
  classical
  exact Finset.card_image_le

theorem contactForceSet_card_le_box {x y : Site d} {D : ℕ}
    (hxy : l1dist d x y = D) :
    (contactForceSet x y).card ≤ (boxFinsetBK d D).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun z : Site d => z - x)
  · intro z hz
    change z - x ∈ boxFinsetBK d D
    rw [mem_boxFinsetBK_iff]
    have hzBetween := (mem_contactForceSet.mp hz).1
    have hdist : l1dist d x z ≤ D :=
      (coordinateBetween_l1dist_le hzBetween).trans_eq hxy
    intro k
    have hterm : (x k - z k).natAbs ≤ l1dist d x z := by
      unfold l1dist
      exact Finset.single_le_sum
        (f := fun j : Fin d => (x j - z j).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have habs : (z k - x k).natAbs = (x k - z k).natAbs := by
      rw [← Int.natAbs_neg]
      congr 1
      ring
    simpa [Pi.sub_apply, habs] using hterm.trans hdist
  · intro a ha b hb hab
    have h := congrArg (fun w : Site d => w + x) hab
    simpa using h


end StatMech.FrontierA
