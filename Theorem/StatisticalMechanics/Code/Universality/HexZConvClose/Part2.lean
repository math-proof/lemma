/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZConvClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Def.StatisticalMechanics.Code.Universality.HexZConvClose.Part2


namespace StatMech.Universality

open scoped BigOperators

open HexWalk


theorem hzc_mem_truncFinset (a : ℂ) (h0 : ℤ) (N : ℕ) (ts : List ℤ) :
    ts ∈ hzc_truncFinset a h0 N ↔
      (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).numVertices < N := by
  unfold hzc_truncFinset
  rw [Set.Finite.mem_toFinset]
  rfl


end StatMech.Universality
