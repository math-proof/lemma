/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKTwoPointQ2Bridge.Part5
import Theorem.StatisticalMechanics.Code.FK.EsCorrelations.Part4
import Theorem.StatisticalMechanics.Code.FK.ThetaZeroBelowPc
import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2
import Theorem.StatisticalMechanics.Code.Ising.TransitionFK
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part2
open scoped BigOperators
open Filter
open MeasureTheory


namespace StatMech

namespace Exact3D

open FK


def FreeQ2FiniteVolumeBoundaryErrorBound
    (β : ℝ) (hβ : 0 < β) (B : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ᶠ N in atTop,
    freeFiniteVolumeOriginBoundaryConnectionOfBetaQ2InVolume β hβ N n ≤ B n


noncomputable def freeQ2BoundaryProfileOfBeta
    (β : ℝ) (hβ : 0 < β) : ℕ → ℝ :=
  fun n =>
    IsingFK.boxBoundaryConnProfile 3
      (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)
      (by norm_num : (0 : ℝ) < 2) n


end Exact3D
end StatMech
