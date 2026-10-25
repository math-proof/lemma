/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellRN.Part5
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part5
import Def.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossing.Part3
open SimpleGraph Set
open scoped BigOperators


namespace StatMech.BeffaraDC

open StatMech.Onsager


@[simp] theorem mem_torusAmbientRotatedEvent (L : ℕ) [Fact (2 < L)]
    {A : Finset (TorusAmbientConfig L)} {omega : TorusAmbientConfig L} :
    omega ∈ torusAmbientRotatedEvent L A ↔
      torusAmbientSwapConfig L omega ∈ A := by
  simp [torusAmbientRotatedEvent]


theorem torusAmbientEventProbability_rotated (L : ℕ) [Fact (2 < L)]
    (p q : ℝ) (A : Finset (TorusAmbientConfig L)) :
    torusAmbientEventProbability L p q (torusAmbientRotatedEvent L A) =
      torusAmbientEventProbability L p q A := by
  unfold torusAmbientEventProbability
  have hsum := Equiv.sum_comp (torusAmbientSwapConfigEquiv L)
    (fun omega : TorusAmbientConfig L =>
      if omega ∈ A then torusAmbientProbability L p q omega else 0)
  simpa [torusAmbientSwapConfigEquiv, mem_torusAmbientRotatedEvent,
    torusAmbientProbability_swap] using hsum


end StatMech.BeffaraDC
