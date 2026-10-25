/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part8


namespace StatMech.Universality

open List


noncomputable def hexHW_bridge_decomp_twoSided :
    ({lower : List HexBridge // StrictIncreasingWidths lower} ×
        {upper : List HexBridge // StrictDecreasingWidths upper}) ≃
      ({γL : List (ℕ × ℤ) // hexHW_IsValidWalk γL} ×
        {γU : List (ℕ × ℤ) // hexHW_IsValidWalk γU}) :=
  
  
  Equiv.prodCongr
    ((Equiv.subtypeEquiv
        (⟨List.reverse, List.reverse, List.reverse_reverse, List.reverse_reverse⟩ :
          List HexBridge ≃ List HexBridge)
        (fun lower => hexHW_strictIncreasing_reverse lower)).trans
      hexHW_bridge_decomp)
    hexHW_bridge_decomp

end StatMech.Universality
