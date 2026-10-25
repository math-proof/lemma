/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailStableKeyPackage
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part6
import Def.StatisticalMechanics.Code.Exact3D.StableKeyTailBridgeExample.Part3
import Def.StatisticalMechanics.Code.Exact3D.GeneratedTableTailBridgeExample.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailStableKeyPackageExample.Part6
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailStableKeyPackageExample

open BoundedPolymerCase

open BoundedPolymerCase.StableKeyCertificateExample

open BoundedPolymerCase.StableKeyTailBridgeExample

open BoundedPolymerCase.GeneratedTableTailBridgeExample

open InfiniteTailTableWitnessPackage


noncomputable def minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    InfiniteTailTableWitnessPackage
      (Case := StableKey K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  (minimalCubicRowsZeroInfiniteTailPackage
    (d := d) K).with_zero_tailEnvelope_and_budgets
      (prefixTailBound' := 1) (tailBound' := 1)
      (zeroSplit_tailEnvelopeOn K ∅)
      (by norm_num)
      (zeroSplit_tailContribution_nonpos_off_support K ∅)
      (by norm_num)


end InfiniteTailStableKeyPackageExample
end Exact3D
end StatMech
