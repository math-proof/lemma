/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveWinding.Part2


namespace StatMech.Onsager

open BigOperators

open StatMech.Onsager.BaseCase

def ons_loopBoundaryCoeff
    {L n : ℕ} [NeZero n]
    (P : (ZMod L × ZMod L) → ZMod 2)
    (v : Fin n → ons_Dart L) (k : Fin n) : ℤ :=
  ons_outgoingBoundaryCoeff P (ons_liftSite v k) (ons_liftDir v k)

end StatMech.Onsager
