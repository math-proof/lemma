/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusDefectComplement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusFKDuality.Part3
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Onsager


def torusHalfTurn (L : ℕ) : (ZMod L × ZMod L) ≃ (ZMod L × ZMod L) :=
  (torusQuarterTurn L).trans (torusQuarterTurn L)

end StatMech.BeffaraDC
