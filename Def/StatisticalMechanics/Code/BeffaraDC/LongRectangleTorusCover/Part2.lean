/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusCover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleGeometry.Part5
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCover.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusCover.Part2
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.Universality


def bdcTorusThinCrossing (L alpha n : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) : Prop :=
  ∃ k : BdcLongRectangleIndex alpha,
    VerticalCrossing (torusPlanarPullback L omega)
      (bdcLongRectangleXOffset n k : ℤ)
      ((bdcLongRectangleXOffset n k : ℤ) + 2 * (n : ℤ))
      (bdcLongRectangleYOffset n k : ℤ)
      ((bdcLongRectangleYOffset n k : ℤ) +
        2 * (alpha : ℤ) * (n : ℤ))


noncomputable def bdcTorusThinCrossingEvent
    (L alpha n : ℕ) [Fact (2 < L)] : Finset (TorusAmbientConfig L) := by
  classical
  exact Finset.univ.filter (bdcTorusThinCrossing L alpha n)

end StatMech.BeffaraDC
