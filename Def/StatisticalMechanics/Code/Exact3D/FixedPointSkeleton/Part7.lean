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
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part6


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

noncomputable def certifiedFixedPointOfL1Contraction {n : ℕ}
    (F : (Fin n → ℝ) → Fin n → ℝ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hLip : LipschitzWithConstant F c) : Fin n → ℝ :=
  (ContractingWith.fixedPoint (L1Vector.liftMap F)
    (contractingWith_liftMap_of_l1_contraction hc_nonneg hc_lt_one hLip)).coord


end FiniteContraction
end Exact3D
end StatMech
