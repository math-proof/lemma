/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part2


namespace StatMech.Universality

open List


def bridgeRecompose (bs : List HexBridge) : List (ℕ × ℤ) :=
  (bs.map HexBridge.rungs).flatten

end StatMech.Universality
