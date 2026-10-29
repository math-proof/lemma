/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Lp.lpSpace
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part7
open scoped BigOperators ENNReal NNReal


namespace StatMech

namespace Exact3D

namespace FinitePlusTailState

variable {n : ℕ} {α : Type*}

theorem lipschitz_equivProduct :
    LipschitzWith 1
      (equivProduct :
        FinitePlusTailState n α →
          FiniteContraction.L1Vector n × SummableTail α) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  rw [Prod.dist_eq]
  have hmax :
      max (FiniteContraction.l1Dist x.finite y.finite)
          (x.tail.dist y.tail) ≤ x.dist y :=
    max_le
      (by simpa [finiteDist] using finiteDist_le_dist x y)
      (by simpa [tailDist] using tailDist_le_dist x y)
  simpa [equivProduct] using hmax


theorem lipschitz_equivProduct_symm :
    LipschitzWith 2
      ((equivProduct :
        FinitePlusTailState n α ≃
          FiniteContraction.L1Vector n × SummableTail α).symm) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  rcases x with ⟨xf, xt⟩
  rcases y with ⟨yf, yt⟩
  rw [Prod.dist_eq]
  change
    FiniteContraction.l1Dist xf.coord yf.coord + xt.dist yt ≤
      ((2 : NNReal) : ℝ) *
        max (FiniteContraction.l1Dist xf.coord yf.coord) (xt.dist yt)
  have hfinite :
      FiniteContraction.l1Dist xf.coord yf.coord ≤
        max (FiniteContraction.l1Dist xf.coord yf.coord) (xt.dist yt) :=
    le_max_left _ _
  have htail :
      xt.dist yt ≤
        max (FiniteContraction.l1Dist xf.coord yf.coord) (xt.dist yt) :=
    le_max_right _ _
  calc
    FiniteContraction.l1Dist xf.coord yf.coord + xt.dist yt ≤
        max (FiniteContraction.l1Dist xf.coord yf.coord) (xt.dist yt) +
          max (FiniteContraction.l1Dist xf.coord yf.coord) (xt.dist yt) :=
      add_le_add hfinite htail
    _ =
        ((2 : NNReal) : ℝ) *
          max (FiniteContraction.l1Dist xf.coord yf.coord) (xt.dist yt) := by
      have htwo : ((2 : NNReal) : ℝ) = (2 : ℝ) := by norm_num
      rw [htwo]
      ring


theorem isUniformEmbedding_equivProduct :
    IsUniformEmbedding
      (equivProduct :
        FinitePlusTailState n α ≃
          FiniteContraction.L1Vector n × SummableTail α) :=
  (equivProduct :
    FinitePlusTailState n α ≃
      FiniteContraction.L1Vector n × SummableTail α).isUniformEmbedding
    lipschitz_equivProduct.uniformContinuous
    lipschitz_equivProduct_symm.uniformContinuous


end FinitePlusTailState
end Exact3D
end StatMech
