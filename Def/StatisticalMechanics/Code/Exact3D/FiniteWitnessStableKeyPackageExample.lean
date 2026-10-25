/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.FiniteWitnessStableKeyPackage
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part6
import Def.StatisticalMechanics.Code.Exact3D.StableKeyTailBridgeExample.Part3
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace FiniteWitnessStableKeyPackageExample

open BoundedPolymerCase

open BoundedPolymerCase.StableKeyCertificateExample

open BoundedPolymerCase.StableKeyTailBridgeExample


noncomputable def rawRowsIndicatorTailPackage {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    FiniteWitnessPackage (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  FiniteWitnessPackage.ofExternalStableKeyRowsFiniteCutoffStableKey
    (finiteBound := (1 : ℝ))
    (tailEnvelopeBound := (support.card : ℝ) * ((1 : ℝ) / 10))
    K (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale (thermal := 3) (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    (indicatorTailSplit (d := d) K support)
    (rawRows d K.radius K.maxDegree K.maxRange)
    zeroInterval (fun _ => (0 : ℝ)) support ∅
    (fun _ => (1 : ℝ) / 10)
    (by simp)
    (indicatorTailSplit_total_zero_off_support K support)
    (indicatorTailSplit_total_nonneg K support)
    (indicatorTailSplit_additive K support)
    (rawRows_cover d K.radius K.maxDegree K.maxRange)
    (indicatorTailSplit_finiteContribution_eq_zero K support)
    (rawRows_row_sound d K.radius K.maxDegree K.maxRange)
    (rawRows_row_upper_one d K.radius K.maxDegree K.maxRange)
    (indicatorTailSplit_tailEnvelopeOn K support)
    (by simp [Finset.sum_const, nsmul_eq_mul])


noncomputable def minimalCubicRowsIndicatorTailPackage {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K)) :
    FiniteWitnessPackage (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  FiniteWitnessPackage.ofExternalStableKeyRowsFiniteCutoffMinimalCubic
    (finiteBound := (1 : ℝ))
    (tailEnvelopeBound := (support.card : ℝ) * ((1 : ℝ) / 10))
    K (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale (thermal := 3) (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    (indicatorTailSplit (d := d) K support)
    (minimalCubicRows d K.radius K.maxDegree K.maxRange)
    zeroInterval (fun _ => (0 : ℝ)) support ∅
    (fun _ => (1 : ℝ) / 10)
    (by simp)
    (indicatorTailSplit_total_zero_off_support K support)
    (indicatorTailSplit_total_nonneg K support)
    (indicatorTailSplit_additive K support)
    (minimalCubicRows_cover d K.radius K.maxDegree K.maxRange)
    (indicatorTailSplit_finiteContribution_eq_zero K support)
    (minimalCubicRows_row_sound d K.radius K.maxDegree K.maxRange)
    (minimalCubicRows_row_upper_one d K.radius K.maxDegree K.maxRange)
    (indicatorTailSplit_tailEnvelopeOn K support)
    (by simp [Finset.sum_const, nsmul_eq_mul])


end FiniteWitnessStableKeyPackageExample
end Exact3D
end StatMech
