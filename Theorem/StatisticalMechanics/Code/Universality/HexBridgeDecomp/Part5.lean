/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part5


namespace StatMech.Universality

open List


theorem hexHW_WF_dropRun (p : ℕ × ℤ) (rest : List (ℕ × ℤ)) (h : hexHW_WF (p :: rest)) :
    hexHW_WF (hexHW_dropRun p rest) :=
  fun q hq => h q ((hexHW_dropRun_sublist p rest).subset hq)


end StatMech.Universality
