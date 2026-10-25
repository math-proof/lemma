/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep.Part5
import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part10
import Theorem.StatisticalMechanics.Code.FK.ActiveEdges.Part4
import Theorem.StatisticalMechanics.Code.Universality.STTTransport.Part3
import Instance.StatisticalMechanics.Code.FK.TriHexFKTorusSweep


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


theorem starFKRepresentativeDirection_open_of_not_closed
    (config : LocalConfig) (h : config ≠ (false, false, false)) :
    triHexLocalDirection config (starFKRepresentativeDirection config) = true := by
  rcases config with ⟨b0, b1, b2⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;>
    simp_all [triHexLocalDirection, starFKRepresentativeDirection]


theorem hexagonalTorus_isolatedCenter_not_adj
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet)
    (z : HexagonalTorusIsolatedCenter L omega) (v : HexTorusVertex L) :
    ¬ (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).Adj (z.1, false) v := by
  rw [hexagonalTorus_openSub_adj_center_iff]
  rintro ⟨i, hi, _hv⟩
  rw [z.2] at hi
  fin_cases i <;> simp [triHexLocalDirection] at hi


end StatMech.FK.PeriodicPlanar
