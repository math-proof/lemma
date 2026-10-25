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
import Def.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part6


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

theorem contractingWith_liftMap_of_l1_contraction {n : ℕ}
    {F : (Fin n → ℝ) → Fin n → ℝ} {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hLip : LipschitzWithConstant F c) :
    ContractingWith (⟨c, hc_nonneg⟩ : ℝ≥0) (L1Vector.liftMap F) := by
  constructor
  · exact_mod_cast hc_lt_one
  · refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    change l1Dist (F x.coord) (F y.coord) ≤
      ((⟨c, hc_nonneg⟩ : ℝ≥0) : ℝ) * l1Dist x.coord y.coord
    simpa using hLip x.coord y.coord


end FiniteContraction
end Exact3D
end StatMech
