/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part37
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem ofFn_even_succ_eq_fkRectBoundaryAlternatingParityList
    (blocks : Nat) :
    List.ofFn (fun i : Fin (2 * blocks + 1) =>
      decide (Even (i.val + 1))) =
        fkRectBoundaryAlternatingParityList blocks := by
  induction blocks with
  | zero => rfl
  | succ blocks ih =>
      rw [show 2 * (blocks + 1) + 1 = (2 * blocks + 2) + 1 by omega]
      rw [List.ofFn_succ]
      change false :: _ = _
      rw [List.ofFn_succ]
      simp only [Fin.val_succ, Fin.val_zero]
      have heven : Even (0 + 1 + 1) := by norm_num
      simp only [heven, decide_true]
      rw [fkRectBoundaryAlternatingParityList]
      simp only [List.cons.injEq, true_and]
      rw [← ih]
      congr 1
      funext i
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      simpa [Nat.add_assoc] using
        (Nat.even_add (m := i.val + 1) (n := 2))

theorem fkRect_nonSeamParityList_eq_alternating
    (R : FKRectTorus) (blocks : Nat)
    (hheight : R.height = 2 * (blocks + 1)) :
    List.ofFn (fun i : Fin (R.height - 1) =>
      decide (Even (fkRectBoundaryNonSeamRow R i).val)) =
        fkRectBoundaryAlternatingParityList blocks := by
  rw [← ofFn_even_succ_eq_fkRectBoundaryAlternatingParityList blocks]
  have hlen : R.height - 1 = 2 * blocks + 1 := by omega
  apply List.ext_get
  · simp [hlen]
  · intro n hn1 hn2
    rw [List.get_ofFn, List.get_ofFn]
    rfl


end
end StatMech.FrontierD
