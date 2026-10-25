/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWindingClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexStripWinding.Part7
import Def.StatisticalMechanics.Code.Universality.HexStripWindingClose.Part2


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


theorem hexUmlauf_band_trivial_bound (a : ℂ) (h0 : ℤ) :
    |hexInfra_headAccum h0 ([] : List ℤ) - (hexUmlauf_band_trivial a h0).H| < 6 := by
  refine hexUmlauf_bound_of_band (fun m => m = a) a h0 a (hexUmlauf_band_trivial a h0)
    ([] : List ℤ) ?_
  refine ⟨trivialWalk_isLegalSAW a h0, ?_, trivialWalk_endMid a h0⟩
  intro m hm
  have hmids : (HexWalk.ofTurns a h0 ([] : List ℤ)).mids = [a] := by
    unfold HexWalk.mids HexWalk.ofTurns; simp only [HexWalk.midsAux_nil]
  rw [hmids, List.mem_singleton] at hm; exact hm


end StatMech.Universality
