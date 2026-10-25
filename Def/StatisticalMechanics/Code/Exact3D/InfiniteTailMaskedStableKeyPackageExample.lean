/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedStableKeyPackage
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailStableKeyPackageExample.Part7
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part6
import Def.StatisticalMechanics.Code.Exact3D.GeneratedTableTailBridgeExample.Part4
import Def.StatisticalMechanics.Code.Exact3D.StableKeyTailBridgeExample.Part3
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailMaskedStableKeyPackageExample

open BoundedPolymerCase

open BoundedPolymerCase.StableKeyCertificateExample

open BoundedPolymerCase.StableKeyTailBridgeExample

open BoundedPolymerCase.GeneratedTableTailBridgeExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailMaskedTableWitnessPackage


noncomputable def rawRowsZeroMaskedTablePackage {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    InfiniteTailMaskedTableWitnessPackage
      (Case := StableKey K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  InfiniteTailMaskedTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffStableKey
    (finiteBound := (0 : ℝ)) (prefixTailBound := (0 : ℝ))
    (tailBound := (0 : ℝ))
    K (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale (thermal := 3) (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    (zeroSplit (d := d) K)
    (rawRows d K.radius K.maxDegree K.maxRange)
    zeroInterval (fun _ => (0 : ℝ)) ∅
    (fun _ => (0 : ℝ))
    (zeroSplit_total_nonneg K)
    (zeroSplit_additive K)
    (rawRows_cover d K.radius K.maxDegree K.maxRange)
    (fun _ => rfl)
    (rawRows_row_sound d K.radius K.maxDegree K.maxRange)
    (rawRows_row_upper_zero d K.radius K.maxDegree K.maxRange)
    (zeroSplit_tailEnvelopeOn K ∅)
    (by simp)
    (by intro _ _; rfl)
    (by intro _ _; simp)
    (by intro _ _; simp [zeroSplit])
    (by simp)
    (by simp)


noncomputable def minimalCubicRowsZeroMaskedTablePackage {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    InfiniteTailMaskedTableWitnessPackage
      (Case := StableKey K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  InfiniteTailMaskedTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffMinimalCubic
    (finiteBound := (0 : ℝ)) (prefixTailBound := (0 : ℝ))
    (tailBound := (0 : ℝ))
    K (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale (thermal := 3) (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    (zeroSplit (d := d) K)
    (minimalCubicRows d K.radius K.maxDegree K.maxRange)
    zeroInterval (fun _ => (0 : ℝ)) ∅
    (fun _ => (0 : ℝ))
    (zeroSplit_total_nonneg K)
    (zeroSplit_additive K)
    (minimalCubicRows_cover d K.radius K.maxDegree K.maxRange)
    (fun _ => rfl)
    (minimalCubicRows_row_sound d K.radius K.maxDegree K.maxRange)
    (minimalCubicRows_row_upper_zero d K.radius K.maxDegree K.maxRange)
    (zeroSplit_tailEnvelopeOn K ∅)
    (by simp)
    (by intro _ _; rfl)
    (by intro _ _; simp)
    (by intro _ _; simp [zeroSplit])
    (by simp)
    (by simp)


noncomputable def rawZeroOneRowsIndicatorMaskedTablePackage {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    InfiniteTailMaskedTableWitnessPackage
      (Case := StableKey K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  InfiniteTailMaskedTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffStableKey
    (finiteBound := (1 : ℝ)) (prefixTailBound := (0 : ℝ))
    (tailBound := (0 : ℝ))
    K (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale (thermal := 3) (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    (keyImageIndicatorSplit support (classifyFiniteCutoffStableKey K))
    (rawZeroOneRows d K.radius K.maxDegree K.maxRange)
    zeroOneInterval
    (keyImageIndicator support (classifyFiniteCutoffStableKey K))
    support (fun _ => (0 : ℝ))
    (keyImageIndicatorSplit_total_nonneg support
      (classifyFiniteCutoffStableKey K))
    (keyImageIndicatorSplit_additive support (classifyFiniteCutoffStableKey K))
    (rawZeroOneRows_cover d K.radius K.maxDegree K.maxRange)
    (fun _ => rfl)
    (rawZeroOneRows_row_sound_keyImageIndicator K support)
    (rawZeroOneRows_row_upper_one d K.radius K.maxDegree K.maxRange)
    (keyImageIndicatorSplit_tailEnvelopeOn_zero support
      (classifyFiniteCutoffStableKey K))
    (zero_tailEnvelope_sum_le support)
    (keyImageIndicatorSplit_finite_zero_off_saturated_support support
      (classifyFiniteCutoffStableKey K) hsaturated)
    (by intro _ _; simp)
    (by intro _ _; simp [keyImageIndicatorSplit])
    (by simp)
    (by simp)


noncomputable def minimalCubicZeroOneRowsIndicatorMaskedTablePackage
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    InfiniteTailMaskedTableWitnessPackage
      (Case := StableKey K.maxDegree K.maxRange)
      (α := FiniteCutoffCoordinate d K)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  InfiniteTailMaskedTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffMinimalCubic
    (finiteBound := (1 : ℝ)) (prefixTailBound := (0 : ℝ))
    (tailBound := (0 : ℝ))
    K (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale (thermal := 3) (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    (keyImageIndicatorSplit support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    (minimalCubicZeroOneRows d K.radius K.maxDegree K.maxRange)
    zeroOneInterval
    (keyImageIndicator support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    support (fun _ => (0 : ℝ))
    (keyImageIndicatorSplit_total_nonneg support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    (keyImageIndicatorSplit_additive support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    (minimalCubicZeroOneRows_cover d K.radius K.maxDegree K.maxRange)
    (fun _ => rfl)
    (minimalCubicZeroOneRows_row_sound_keyImageIndicator K support)
    (minimalCubicZeroOneRows_row_upper_one
      d K.radius K.maxDegree K.maxRange)
    (keyImageIndicatorSplit_tailEnvelopeOn_zero support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    (zero_tailEnvelope_sum_le support)
    (keyImageIndicatorSplit_finite_zero_off_saturated_support support
      (classifyFiniteCutoffMinimalCubicStableKey K) hsaturated)
    (by intro _ _; simp)
    (by intro _ _; simp [keyImageIndicatorSplit])
    (by simp)
    (by simp)


end InfiniteTailMaskedStableKeyPackageExample
end Exact3D
end StatMech
