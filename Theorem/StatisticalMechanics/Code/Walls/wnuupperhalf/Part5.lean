module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
public import Theorem.StatisticalMechanics.Code.Walls.umffullrev.Part2
public import Theorem.StatisticalMechanics.Code.Walls.wndwinding.Part3
public import Def.StatisticalMechanics.Code.Walls.wnuupperhalf.Part5
open Finset Set SimpleGraph
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

theorem wnu_Ltromino_signedList :
    wnu_signedList (![1, 1] : Site 2) wnu_LtrominoLoop = [-1] := by
  unfold wnu_signedList wnu_LtrominoLoop
  simp only [SimpleGraph.Walk.darts_append, SimpleGraph.Walk.darts_copy,
    SimpleGraph.Walk.darts_reverse, List.map_append, List.map_reverse, List.map_map]
  decide


theorem wnu_Ltromino_alternates :
    wnu_Alternates (![1, 1] : Site 2) wnu_LtrominoLoop := by
  unfold wnu_Alternates
  rw [wnu_Ltromino_signedList]
  exact Or.inr rfl


theorem wnu_Ltromino_signedCross_abs_le_one :
    |wnd_signedCross (![1, 1] : Site 2) wnu_LtrominoLoop| ≤ 1 :=
  wnu_signedCross_abs_le_one_of_alternates _ _ wnu_Ltromino_alternates


end Lattice
end StatMech
