/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripInterior.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexW1ExitGeom.Part5
import Def.StatisticalMechanics.Code.Universality.HexStripInterior.Part4


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


theorem hexStrip_singleRight_dirMids (a : ℂ) (h0 : ℤ) :
    hexStripDirMids a h0 [(-1 : ℤ)]
      = [(a, h0), (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1)), h0 + (-1))] := by
  rw [hexStripDirMids_cons, hexStripDirMids_nil]


theorem hexStrip_singleRight_staysInDir (a : ℂ) (h0 : ℤ) :
    hexStripStaysInDir (hexStrip_singleRightDReg a h0) a h0 [(-1 : ℤ)] := by
  intro p hp
  rw [hexStrip_singleRight_dirMids] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩


theorem hexStrip_singleRight_interior_fires (a : ℂ) (h0 : ℤ) :
    hexStripInterior (hexStrip_singleRightDReg a h0) (a + HexWalk.halfStep h0) := by
  apply hexStrip_interiorVertices_core (hexStrip_singleRightDReg a h0) a h0 [(-1 : ℤ)]
    (hexW1Exit_singleRight_legal a h0) (hexStrip_singleRight_staysInDir a h0)
  · 
    have hverts : (HexWalk.ofTurns a h0 [(-1 : ℤ)]).vertices
        = [a + HexWalk.halfStep h0,
            a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))
              + HexWalk.halfStep (h0 + (-1))] := by
      unfold HexWalk.ofTurns HexWalk.vertices; simp [HexWalk.verticesAux]
    rw [hverts]; exact List.mem_cons_self
  · 
    have hlast : hexInfra_midAccum a h0 [(-1 : ℤ)]
          + HexWalk.halfStep (hexInfra_headAccum h0 [(-1 : ℤ)])
        = a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))
            + HexWalk.halfStep (h0 + (-1)) := by
      simp only [hexInfra_midAccum_cons, hexInfra_midAccum_nil, hexInfra_headAccum_cons,
        hexInfra_headAccum_nil]
    rw [hlast]
    intro hc
    have h2 : (2 : ℂ) * HexWalk.halfStep (h0 + (-1)) = 0 := by linear_combination -hc
    rcases mul_eq_zero.mp h2 with hh | hh
    · norm_num at hh
    · exact hexW1Exit_halfStep_ne_zero (h0 + (-1)) hh


theorem hexStrip_singleRight_uniqueInterior (a : ℂ) (h0 : ℤ) (h : ℤ)
    (hint : hexStripInterior (hexStrip_singleRightDReg a h0)
      ((a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) + HexWalk.halfStep h)) :
    HexWalk.halfStep h = HexWalk.halfStep ((h0 - 1) + 3) := by
  set z := a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1)) with hzdef
  obtain ⟨m1, m2, d1, d2, hr1, hr2, hne, hi1, hi2⟩ := hint
  
  have key : hexIncident (z + HexWalk.halfStep h) a h0
      → HexWalk.halfStep h = HexWalk.halfStep ((h0 - 1) + 3) := by
    intro hi
    rcases hi with hi | hi
    · rw [hzdef] at hi
      rw [show ((h0 - 1) + 3 : ℤ) = (h0 + (-1)) + 3 by ring, hexW1Exit_halfStep_add_three]
      linear_combination hi
    · rw [hzdef] at hi; exact absurd hi.symm (hexStrip_outer_ne a h0 h)
  
  unfold hexStrip_singleRightDReg at hr1 hr2
  rcases hr1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact key hi1
  · rcases hr2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact key hi2
    · exact absurd rfl hne


end StatMech.Universality
