/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
import Theorem.StatisticalMechanics.Code.Universality.HexW1Sides.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexW1ExitGeom.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexW1HeadingWindow.Part4
import Def.StatisticalMechanics.Code.Universality.HexStripWinding.Part4


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


theorem hexStripWinding_trivial_bound (a : ℂ) (h0 : ℤ) :
    |hexInfra_headAccum h0 ([] : List ℤ) - (hexStripWinding_trivial a h0).H| < 6 := by
  refine (hexStripWinding_trivial a h0).bound ([] : List ℤ) ?_
  refine ⟨trivialWalk_isLegalSAW a h0, ?_, trivialWalk_endMid a h0⟩
  intro m hm
  have hmids : (HexWalk.ofTurns a h0 ([] : List ℤ)).mids = [a] := by
    unfold HexWalk.mids HexWalk.ofTurns; simp only [HexWalk.midsAux_nil]
  rw [hmids, List.mem_singleton] at hm; exact hm


end StatMech.Universality
