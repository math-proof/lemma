/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusPushforward.Part6
import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTranslationClosure.Part3
open MeasureTheory SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.Universality


def bdcTorusCanonicalShift {L : ℕ} (u : ZMod L × ZMod L) : Site 2 :=
  ![(u.1.val : ℤ), (u.2.val : ℤ)]

end StatMech.BeffaraDC
