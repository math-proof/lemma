/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.TrivalentCycles
import Theorem.StatisticalMechanics.Code.Onsager.TurningTelescope.Part3
import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Def.StatisticalMechanics.Code.Onsager.TorusDecoration.Part3


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

theorem ons_decGraph_neighborFinset (L : ℕ) [NeZero L] (d : ons_Dart L) :
    (ons_decGraph L).neighborFinset d =
      insert (ons_dartRev L d) (ons_decInternalNeighbors d) := by
  ext e
  rw [SimpleGraph.mem_neighborFinset]
  rcases d with ⟨s, mu⟩
  rcases e with ⟨t, nu⟩
  fin_cases mu <;> fin_cases nu <;>
    simp [ons_decGraph, ons_decAdj, ons_decInternalAdj,
      ons_decInternalNeighbors, eq_comm]


theorem ons_decGraph_degree_le_three (L : ℕ) [NeZero L] (d : ons_Dart L) :
    (ons_decGraph L).degree d ≤ 3 := by
  change ((ons_decGraph L).neighborFinset d).card ≤ 3
  rw [ons_decGraph_neighborFinset]
  refine (Finset.card_insert_le _ _).trans ?_
  rcases d with ⟨s, mu⟩
  fin_cases mu <;> simp [ons_decInternalNeighbors]


end StatMech.Onsager
