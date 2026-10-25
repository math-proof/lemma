/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.umffullrev.Part2
import Theorem.StatisticalMechanics.Code.Walls.wndwinding.Part3
import Def.StatisticalMechanics.Code.Walls.wnuupperhalf.Part4
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

theorem wnu_doubleSquare_signedList :
    wnu_signedList (![1, 1] : Site 2) wnu_doubleSquare = [1, 1] := by
  unfold wnu_doubleSquare wnu_signedList wwit_unitSquareLoop
  simp only [SimpleGraph.Walk.darts_append, SimpleGraph.Walk.darts_copy,
    SimpleGraph.Walk.darts_reverse, List.map_append, List.map_reverse, List.map_map]
  decide


theorem wnu_doubleSquare_not_alternates :
    ¬ wnu_Alternates (![1, 1] : Site 2) wnu_doubleSquare := by
  unfold wnu_Alternates
  rw [wnu_doubleSquare_signedList]
  exact wnu_not_alt_oneOne


theorem wnu_doubleSquare_signedCross_two :
    wnd_signedCross (![1, 1] : Site 2) wnu_doubleSquare = 2 := by
  unfold wnu_doubleSquare
  rw [wnd_signedCross_append, wnd_unitSquareLoop_signedCross]; norm_num


theorem wnu_doubleSquare_not_pm_one :
    ¬ (wnd_signedCross (![1, 1] : Site 2) wnu_doubleSquare = 1 ∨
       wnd_signedCross (![1, 1] : Site 2) wnu_doubleSquare = -1) := by
  rw [wnu_doubleSquare_signedCross_two]; decide


end Lattice
end StatMech
