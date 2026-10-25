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
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossing.Part5
open SimpleGraph Set
open scoped BigOperators


namespace StatMech.BeffaraDC

open StatMech.Onsager


noncomputable def torusSquareVerticalCrossingEvent
    (L : ℕ) [Fact (2 < L)] (n : ℕ) : Finset (TorusAmbientConfig L) :=
  torusAmbientRotatedEvent L (torusSquareHorizontalCrossingEvent L n)

end StatMech.BeffaraDC
