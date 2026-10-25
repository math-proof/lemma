/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeWeight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeWeight


namespace StatMech.Universality

open List

open scoped BigOperators


noncomputable def hbw_widthFinset (bs : List HexBridge) : Finset ℕ :=
  (bs.map HexBridge.width).toFinset


end StatMech.Universality
