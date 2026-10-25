/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Instance.StatisticalMechanics.Code.FK.TriHexTorusDuality
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

theorem zmod_one_ne_zero (L : ℕ) [Fact (2 < L)] :
    (1 : ZMod L) ≠ 0 := by
  have h : ((1 : ℕ) : ZMod L) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hle := Nat.le_of_dvd (by norm_num : 0 < 1) hdvd
    have := (Fact.out : 2 < L)
    omega
  simpa using h

theorem zmod_two_ne_zero (L : ℕ) [Fact (2 < L)] :
    (2 : ZMod L) ≠ 0 := by
  have h : ((2 : ℕ) : ZMod L) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
    have := (Fact.out : 2 < L)
    omega
  simpa using h


end PeriodicPlanar
end FK
end StatMech
