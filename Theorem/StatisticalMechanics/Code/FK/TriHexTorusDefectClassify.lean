/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part10
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusConnected
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.EulerComponentCount.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open StatMech.Lattice

open StatMech.Onsager

theorem triHex_zmod_one_ne_zero (L : ℕ) [Fact (2 < L)] :
    (1 : ZMod L) ≠ 0 := by
  rw [Ne, ← Nat.cast_one, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have hle := Nat.le_of_dvd (by norm_num : 0 < 1) hdvd
  have := (Fact.out : 2 < L)
  omega


end PeriodicPlanar
end FK
end StatMech
