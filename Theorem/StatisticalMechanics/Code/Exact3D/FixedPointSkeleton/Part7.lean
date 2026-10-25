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
import Def.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part7


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

theorem certifiedFixedPointOfL1Contraction_isFixed {n : ℕ}
    (F : (Fin n → ℝ) → Fin n → ℝ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hLip : LipschitzWithConstant F c) :
    F (certifiedFixedPointOfL1Contraction F hc_nonneg hc_lt_one hLip) =
      certifiedFixedPointOfL1Contraction F hc_nonneg hc_lt_one hLip := by
  let hcontract :=
    contractingWith_liftMap_of_l1_contraction
      (F := F) hc_nonneg hc_lt_one hLip
  have hfixed :
      Function.IsFixedPt (L1Vector.liftMap F)
        (ContractingWith.fixedPoint (L1Vector.liftMap F) hcontract) :=
    hcontract.fixedPoint_isFixedPt
  simpa [certifiedFixedPointOfL1Contraction, L1Vector.liftMap,
    L1Vector.ofFun, Function.IsFixedPt] using congrArg L1Vector.coord hfixed


theorem exists_fixedPoint_of_l1_contraction {n : ℕ}
    (F : (Fin n → ℝ) → Fin n → ℝ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hLip : LipschitzWithConstant F c) :
    ∃ p : Fin n → ℝ, F p = p :=
  ⟨certifiedFixedPointOfL1Contraction F hc_nonneg hc_lt_one hLip,
    certifiedFixedPointOfL1Contraction_isFixed F hc_nonneg hc_lt_one hLip⟩


theorem lipschitz_iterate {n : ℕ} {F : (Fin n → ℝ) → Fin n → ℝ} {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hLip : LipschitzWithConstant F c) (k : ℕ) :
    LipschitzWithConstant (iterate F k) (c ^ k) := by
  induction k with
  | zero =>
      intro x y
      simp [iterate]
  | succ k ih =>
      intro x y
      calc
        l1Dist (iterate F (k + 1) x) (iterate F (k + 1) y) =
            l1Dist (F (iterate F k x)) (F (iterate F k y)) := rfl
        _ ≤ c * l1Dist (iterate F k x) (iterate F k y) := hLip _ _
        _ ≤ c * (c ^ k * l1Dist x y) := by
          exact mul_le_mul_of_nonneg_left (ih x y) hc_nonneg
        _ = c ^ (k + 1) * l1Dist x y := by
          ring


end FiniteContraction
end Exact3D
end StatMech
