/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Structure.StatisticalMechanics.Code.Universality.HexBridge.Part4


namespace StatMech.Universality

open Filter Topology

open scoped Topology BigOperators


namespace HexHighestCut

variable {K : ℝ}


theorem recursion_bound (H : HexHighestCut K) (hK : 0 ≤ K) :
    (∑' d, H.wtγ d) ≤ K * (∑' b, H.wtB b) ^ 2 := by
  
  have hprodSumm : Summable (fun p : H.B × H.B => H.wtB p.1 * H.wtB p.2) :=
    H.B_summable.mul_of_nonneg H.B_summable H.wtB_nn H.wtB_nn
  have hprodEq : (∑' p : H.B × H.B, H.wtB p.1 * H.wtB p.2) = (∑' b, H.wtB b) ^ 2 := by
    rw [sq, ← H.B_summable.tsum_mul_tsum H.B_summable hprodSumm]
  
  have hcompSumm : Summable (fun d => H.wtB (H.split d).1 * H.wtB (H.split d).2) :=
    hprodSumm.comp_injective H.split_inj
  have hcompLe :
      (∑' d, H.wtB (H.split d).1 * H.wtB (H.split d).2)
        ≤ ∑' p : H.B × H.B, H.wtB p.1 * H.wtB p.2 := by
    have := Summable.tsum_le_tsum_of_inj H.split H.split_inj
      (fun c _ => mul_nonneg (H.wtB_nn c.1) (H.wtB_nn c.2)) (fun _ => le_refl _)
      hcompSumm hprodSumm
    simpa using this
  calc (∑' d, H.wtγ d)
      ≤ ∑' d, K * (H.wtB (H.split d).1 * H.wtB (H.split d).2) :=
        H.D_summable.tsum_mono (hcompSumm.mul_left K) H.weight_bound
    _ = K * ∑' d, H.wtB (H.split d).1 * H.wtB (H.split d).2 := tsum_mul_left
    _ ≤ K * (∑' p : H.B × H.B, H.wtB p.1 * H.wtB p.2) :=
        mul_le_mul_of_nonneg_left hcompLe hK
    _ = K * (∑' b, H.wtB b) ^ 2 := by rw [hprodEq]

end HexHighestCut
end StatMech.Universality
