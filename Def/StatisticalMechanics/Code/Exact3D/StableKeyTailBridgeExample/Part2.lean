/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyTailBridge.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyCertificateExample.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyTailBridgeExample
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

namespace StableKeyTailBridgeExample

noncomputable def emptyFiniteCutoffCoordinate (d : ℕ) (K : TailCutoff) :
    FiniteCutoffCoordinate d K :=
  ⟨{ support := PolymerSupport.empty d,
      degree := 0,
      range := 0,
      symmetry :=
        { translationQuotiented := false,
          cubicQuotiented := false,
          spinFlipEven := false } }, by
    simp [InsideFiniteCutoff]⟩


noncomputable def singletonEmptySupport {d : ℕ} (K : TailCutoff) :
    Finset (FiniteCutoffCoordinate d K) :=
  {emptyFiniteCutoffCoordinate d K}


noncomputable def indicatorTailSplit {d : ℕ} (K : TailCutoff)
    (support : Finset (FiniteCutoffCoordinate d K)) :
    ContributionSplit (FiniteCutoffCoordinate d K) where
  finiteContribution := fun _ => 0
  tailContribution := by
    classical
    exact fun a => if a ∈ support then (1 : ℝ) / 10 else 0
  totalContribution := by
    classical
    exact fun a => if a ∈ support then (1 : ℝ) / 10 else 0


end StableKeyTailBridgeExample
end BoundedPolymerCase
end Exact3D
end StatMech
