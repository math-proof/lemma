/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1ExitGeom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
import Theorem.StatisticalMechanics.Code.Universality.HexW1Sides.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexW1ExitGeom.Part4


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


noncomputable def hexW1Exit_singleRight_straightSide (a : ℂ) (h0 : ℤ) (inReg : ℂ → Prop)
    (hclass : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inReg
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt
            (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) → ts = [(-1 : ℤ)]) :
    HexStraightSide inReg (fun v => v = a + HexWalk.halfStep h0) a h0
      (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) where
  H := h0 - 1
  uniqueInterior := by
    intro h hint
    have hh : HexWalk.halfStep h = - HexWalk.halfStep (h0 + (-1)) := by linear_combination hint
    rw [hh, show (h0 + (-1) : ℤ) = h0 - 1 by ring, hexW1Exit_halfStep_add_three]
  interiorVertices := by
    intro ts hadm v hv hvne
    have hts : ts = [(-1 : ℤ)] := hclass ts hadm
    subst hts
    have hverts : (HexWalk.ofTurns a h0 [(-1 : ℤ)]).vertices
        = [a + HexWalk.halfStep h0,
            a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1)) + HexWalk.halfStep (h0 + (-1))] := by
      unfold HexWalk.ofTurns HexWalk.vertices; simp [HexWalk.verticesAux]
    rw [hverts] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h
    · exact h
    · exfalso; apply hvne
      rw [h, hexInfra_headAccum_cons, hexInfra_headAccum_nil,
        show (h0 + (-1) : ℤ) = h0 + (-1) from rfl]


end StatMech.Universality
