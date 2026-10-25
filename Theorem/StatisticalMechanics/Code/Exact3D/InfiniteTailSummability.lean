/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton.Part5
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace TailSummability

variable {α : Type*} [DecidableEq α]


namespace InfiniteTailCertificate

variable (C : InfiniteTailCertificate α)


theorem summable_prefixWeight : Summable C.prefixWeight :=
  summable_of_ne_finset_zero (s := C.finitePrefix)
    C.prefixWeight_zero_off_prefix


theorem tsum_prefixWeight_eq_prefixWeight_sum :
    (∑' a, C.prefixWeight a) =
      ∑ a ∈ C.finitePrefix, C.prefixWeight a :=
  tsum_eq_sum (s := C.finitePrefix) C.prefixWeight_zero_off_prefix


theorem prefixWeight_sum_eq_prefixSum :
    (∑ a ∈ C.finitePrefix, C.prefixWeight a) = C.prefixSum := by
  unfold prefixSum
  exact Finset.sum_congr rfl fun a ha => C.prefix_eq_weight_on_prefix a ha


theorem tsum_prefixWeight_eq_prefixSum :
    (∑' a, C.prefixWeight a) = C.prefixSum := by
  rw [C.tsum_prefixWeight_eq_prefixWeight_sum,
    C.prefixWeight_sum_eq_prefixSum]


theorem summable_weight : Summable C.weight := by
  have hsum :
      Summable (fun a => C.prefixWeight a + C.tailWeight a) :=
    C.summable_prefixWeight.add C.summable_tail
  exact hsum.congr fun a => (C.decomposition a).symm


theorem tsum_weight_eq_prefixSum_add_tail :
    (∑' a, C.weight a) =
      C.prefixSum + ∑' a, C.tailWeight a := by
  calc
    (∑' a, C.weight a) =
        ∑' a, (C.prefixWeight a + C.tailWeight a) :=
      tsum_congr C.decomposition
    _ = (∑' a, C.prefixWeight a) + ∑' a, C.tailWeight a :=
      Summable.tsum_add C.summable_prefixWeight C.summable_tail
    _ = C.prefixSum + ∑' a, C.tailWeight a := by
      rw [C.tsum_prefixWeight_eq_prefixSum]


theorem tsum_weight_le_prefixSum_add_tailBound :
    (∑' a, C.weight a) ≤ C.prefixSum + C.tailBound := by
  rw [C.tsum_weight_eq_prefixSum_add_tail]
  exact add_le_add (le_refl C.prefixSum) C.tail_tsum_le


theorem tsum_weight_le_prefixSum_add_of_tailBound_le {tailBound' : ℝ}
    (hle : C.tailBound ≤ tailBound') :
    (∑' a, C.weight a) ≤ C.prefixSum + tailBound' :=
  le_trans C.tsum_weight_le_prefixSum_add_tailBound
    (add_le_add (le_refl C.prefixSum) hle)


theorem prefixSum_nonneg : 0 ≤ C.prefixSum := by
  unfold prefixSum
  exact sum_nonneg_on fun a ha => by
    rw [← C.prefix_eq_weight_on_prefix a ha]
    exact C.prefixWeight_nonneg a


theorem tail_tsum_nonneg : 0 ≤ ∑' a, C.tailWeight a :=
  tsum_nonneg C.tailWeight_nonneg


theorem tsum_weight_nonneg : 0 ≤ ∑' a, C.weight a := by
  rw [C.tsum_weight_eq_prefixSum_add_tail]
  exact add_nonneg C.prefixSum_nonneg C.tail_tsum_nonneg


theorem tailBound_nonneg : 0 ≤ C.tailBound :=
  le_trans C.tail_tsum_nonneg C.tail_tsum_le


theorem weight_nonneg (a : α) : 0 ≤ C.weight a := by
  rw [C.decomposition a]
  exact add_nonneg (C.prefixWeight_nonneg a) (C.tailWeight_nonneg a)


end InfiniteTailCertificate
end TailSummability
end Exact3D
end StatMech
