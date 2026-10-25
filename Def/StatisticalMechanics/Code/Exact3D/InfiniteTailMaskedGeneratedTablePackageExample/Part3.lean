/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedGeneratedTablePackage
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part6
import Def.StatisticalMechanics.Code.Exact3D.GeneratedTableTailBridgeExample.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.Part2
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailMaskedGeneratedTablePackageExample

open BoundedPolymerCase

open BoundedPolymerCase.GeneratedTableTailBridgeExample

open InfiniteTailMaskedTableWitnessPackage


noncomputable def generatedCubicClassMaskedTablePackage_replacedTailEnvelope
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    InfiniteTailMaskedTableWitnessPackage
      (Case := CubicClass d K.radius K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  (generatedCubicClassMaskedTablePackage
    (d := d) K support hsaturated).with_zero_tailEnvelope_and_budgets
      (prefixTailBound' := 2) (tailBound' := 0)
      (keyImageIndicatorSplit_tailEnvelopeOn_zero support
        (classifyFiniteCutoffCubicClass K))
      (by norm_num)
      (keyImageIndicatorSplit_tailContribution_nonpos_off_support support
        (classifyFiniteCutoffCubicClass K))
      (by norm_num)


end InfiniteTailMaskedGeneratedTablePackageExample
end Exact3D
end StatMech
