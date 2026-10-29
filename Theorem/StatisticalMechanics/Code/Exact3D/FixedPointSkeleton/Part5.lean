/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.UniformSpace.Pi
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
import Def.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part5


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

namespace L1Vector

variable {n : ℕ}


theorem pi_dist_le_l1Dist {n : ℕ} (x y : Fin n → ℝ) :
    dist x y ≤ l1Dist x y := by
  rw [dist_pi_le_iff (l1Dist_nonneg x y)]
  intro i
  simpa [Real.dist_eq] using abs_sub_coord_le_l1Dist x y i


theorem l1Dist_le_nat_mul_pi_dist {n : ℕ} (x y : Fin n → ℝ) :
    l1Dist x y ≤ (n : ℝ) * dist x y := by
  unfold l1Dist RatInterval.supNormVec
  calc
    (∑ i, |x i - y i|) = ∑ i, dist (x i) (y i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [Real.dist_eq]
    _ ≤ ∑ _i : Fin n, dist x y := by
      exact Finset.sum_le_sum fun i _ => dist_le_pi_dist x y i
    _ = (n : ℝ) * dist x y := by
      simp [Finset.sum_const, nsmul_eq_mul]


theorem lipschitz_coord {n : ℕ} :
    LipschitzWith 1 (fun x : L1Vector n => x.coord) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  change dist x.coord y.coord ≤ (1 : NNReal) * l1Dist x.coord y.coord
  simpa using pi_dist_le_l1Dist x.coord y.coord


theorem lipschitz_ofFun {n : ℕ} :
    LipschitzWith (n : NNReal) (ofFun : (Fin n → ℝ) → L1Vector n) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  change l1Dist x y ≤ ((n : NNReal) : ℝ) * dist x y
  simpa using l1Dist_le_nat_mul_pi_dist x y


theorem isUniformEmbedding_equivFun (n : ℕ) :
    IsUniformEmbedding (equivFun n) :=
  (equivFun n).isUniformEmbedding
    (lipschitz_coord (n := n)).uniformContinuous
    (lipschitz_ofFun (n := n)).uniformContinuous


end L1Vector
end FiniteContraction
end Exact3D
end StatMech
