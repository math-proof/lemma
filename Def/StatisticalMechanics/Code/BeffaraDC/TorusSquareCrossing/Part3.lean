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
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossing.Part2
open SimpleGraph Set
open scoped BigOperators


namespace StatMech.BeffaraDC

open StatMech.Onsager


noncomputable def torusAmbientEventProbability (L : ℕ) [Fact (2 < L)]
    (p q : ℝ) (A : Finset (TorusAmbientConfig L)) : ℝ :=
  ∑ omega : TorusAmbientConfig L,
    if omega ∈ A then torusAmbientProbability L p q omega else 0


noncomputable def torusAmbientRotatedEvent (L : ℕ) [Fact (2 < L)]
    (A : Finset (TorusAmbientConfig L)) : Finset (TorusAmbientConfig L) :=
  Finset.univ.filter fun omega => torusAmbientSwapConfig L omega ∈ A

end StatMech.BeffaraDC
