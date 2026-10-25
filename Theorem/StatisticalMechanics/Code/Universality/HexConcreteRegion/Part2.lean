/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexPairingMaps.Part4
import Def.StatisticalMechanics.Code.Universality.HexConcreteRegion


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators


theorem hexConcreteDu_ne (a : ℂ) (h0 : ℤ) : hexConcreteDu a h0 ≠ 0 :=
  hexConcrete_du_ne h0


theorem hexConcrete_p_eq (a : ℂ) (h0 : ℤ) :
    hexConcreteV a h0 + hexConcreteDu a h0 = a := by
  unfold hexConcreteV hexConcreteDu; ring


theorem hexConcrete_endsAt_p (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 []).EndsAt (hexConcreteV a h0 + hexConcreteDu a h0) := by
  unfold HexWalk.EndsAt
  rw [show (ofTurns a h0 []).endMid = (trivialWalk a h0).endMid from rfl,
    trivialWalk_endMid a h0, hexConcrete_p_eq]


theorem hexConcrete_endsAt_q (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 [-1]).EndsAt (hexConcreteQ a h0) := by
  unfold HexWalk.EndsAt hexConcreteQ hexConcreteV hexConcreteDu
  rw [show ([-1] : List ℤ) = [(-1 : ℤ)] from rfl, hexConcrete_endMid_one,
    show (h0 + (-1) : ℤ) = h0 - 1 by ring, hexConcrete_halfStep_sub]
  ring


theorem hexConcrete_endsAt_r (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 [1]).EndsAt (hexConcreteR a h0) := by
  unfold HexWalk.EndsAt hexConcreteR hexConcreteV hexConcreteDu
  rw [show ([1] : List ℤ) = [(1 : ℤ)] from rfl, hexConcrete_endMid_one,
    hexConcrete_halfStep_add]
  ring


theorem hexConcrete_a_ne_q (a : ℂ) (h0 : ℤ) : a ≠ hexConcreteQ a h0 := by
  have := hexMid_p_ne_q (v := hexConcreteV a h0) (du := hexConcreteDu a h0) (hexConcreteDu_ne a h0)
  rwa [hexConcrete_p_eq] at this


theorem hexConcrete_a_ne_r (a : ℂ) (h0 : ℤ) : a ≠ hexConcreteR a h0 := by
  have := hexMid_p_ne_r (v := hexConcreteV a h0) (du := hexConcreteDu a h0) (hexConcreteDu_ne a h0)
  rwa [hexConcrete_p_eq] at this


theorem hexConcrete_q_ne_r (a : ℂ) (h0 : ℤ) : hexConcreteQ a h0 ≠ hexConcreteR a h0 :=
  hexMid_q_ne_r (v := hexConcreteV a h0) (du := hexConcreteDu a h0) (hexConcreteDu_ne a h0)


theorem hexConcrete_mids_qext (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 [-1]).mids = [a, hexConcreteQ a h0] := by
  rw [show ([-1] : List ℤ) = [(-1 : ℤ)] from rfl, hexConcrete_mids_one]
  unfold hexConcreteQ hexConcreteV hexConcreteDu
  rw [show (h0 + (-1) : ℤ) = h0 - 1 by ring, hexConcrete_halfStep_sub]
  congr 2; ring


theorem hexConcrete_mids_rext (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 [1]).mids = [a, hexConcreteR a h0] := by
  rw [show ([1] : List ℤ) = [(1 : ℤ)] from rfl, hexConcrete_mids_one]
  unfold hexConcreteR hexConcreteV hexConcreteDu
  rw [hexConcrete_halfStep_add]
  congr 2; ring


theorem hexConcrete_qext_not_passes_r (a : ℂ) (h0 : ℤ) :
    ¬ PassesThrough a h0 [-1] (hexConcreteR a h0) := by
  unfold PassesThrough
  rw [hexConcrete_mids_qext]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro (hr | hr)
  · exact hexConcrete_a_ne_r a h0 hr.symm
  · exact hexConcrete_q_ne_r a h0 hr.symm


theorem hexConcrete_rext_not_passes_q (a : ℂ) (h0 : ℤ) :
    ¬ PassesThrough a h0 [1] (hexConcreteQ a h0) := by
  unfold PassesThrough
  rw [hexConcrete_mids_rext]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro (hq | hq)
  · exact hexConcrete_a_ne_q a h0 hq.symm
  · exact hexConcrete_q_ne_r a h0 hq


theorem hexConcrete_atoms (a : ℂ) (h0 : ℤ) :
    ((ofTurns a h0 []).IsLegalSAW
        ∧ (ofTurns a h0 []).EndsAt (hexConcreteV a h0 + hexConcreteDu a h0))
      ∧ ((ofTurns a h0 [-1]).IsLegalSAW
          ∧ (ofTurns a h0 [-1]).EndsAt (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0))
      ∧ ((ofTurns a h0 [1]).IsLegalSAW
          ∧ (ofTurns a h0 [1]).EndsAt (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0))
      ∧ (¬ PassesThrough a h0 [-1] (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0))
      ∧ (¬ PassesThrough a h0 [1] (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0)) := by
  refine ⟨⟨trivialWalk_isLegalSAW a h0, hexConcrete_endsAt_p a h0⟩,
    ⟨hexConcrete_legalSAW_one a h0 (-1) (Or.inr rfl), hexConcrete_endsAt_q a h0⟩,
    ⟨hexConcrete_legalSAW_one a h0 1 (Or.inl rfl), hexConcrete_endsAt_r a h0⟩, ?_, ?_⟩
  · exact hexConcrete_qext_not_passes_r a h0
  · exact hexConcrete_rext_not_passes_q a h0


theorem hexConcrete_q_canon (a : ℂ) (h0 : ℤ) :
    hexConcreteQ a h0 = a + (((1 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  unfold hexConcreteQ hexConcreteV hexConcreteDu; push_cast; ring


theorem hexConcrete_r_canon (a : ℂ) (h0 : ℤ) :
    hexConcreteR a h0 = a + (((2 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  unfold hexConcreteR hexConcreteV hexConcreteDu
  rw [hexConcrete_omega_cubic]; push_cast; ring


theorem hexConcrete_endMid_mm (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 [-1, -1]).endMid
      = a + (((0 : ℝ) : ℂ) + ((-3 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  rw [hexConcrete_endMid_two, show (h0 + (-1) + (-1) : ℤ) = h0 - 2 by ring,
    hexConcrete_halfStep_sub2, show (h0 + (-1) : ℤ) = h0 - 1 by ring,
    hexConcrete_halfStep_sub, hexConcrete_omega_cubic]
  push_cast; ring


theorem hexConcrete_endMid_mp (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 [-1, 1]).endMid
      = a + (((2 : ℝ) : ℂ) + ((-2 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  rw [hexConcrete_endMid_two, show (h0 + (-1) + 1 : ℤ) = h0 by ring,
    show (h0 + (-1) : ℤ) = h0 - 1 by ring, hexConcrete_halfStep_sub]
  push_cast; ring


theorem hexConcrete_endMid_pm (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 [1, -1]).endMid
      = a + (((4 : ℝ) : ℂ) + ((2 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  rw [hexConcrete_endMid_two, show (h0 + 1 + (-1) : ℤ) = h0 by ring,
    hexConcrete_halfStep_add, hexConcrete_omega_cubic]
  push_cast; ring


theorem hexConcrete_endMid_pp (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 [1, 1]).endMid
      = a + (((3 : ℝ) : ℂ) + ((3 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  rw [hexConcrete_endMid_two, show (h0 + 1 + 1 : ℤ) = h0 + 2 by ring,
    hexConcrete_halfStep_add2, hexConcrete_halfStep_add, hexConcrete_omega_cubic]
  push_cast; ring


theorem hexConcrete_a_canon (a : ℂ) (h0 : ℤ) :
    a = a + (((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  push_cast; ring


theorem hexConcrete_len2_endMid_not_mid (a : ℂ) (h0 : ℤ) (t1 t2 : ℤ)
    (h1 : t1 = 1 ∨ t1 = -1) (h2 : t2 = 1 ∨ t2 = -1) :
    (ofTurns a h0 [t1, t2]).endMid ≠ a
      ∧ (ofTurns a h0 [t1, t2]).endMid ≠ hexConcreteQ a h0
      ∧ (ofTurns a h0 [t1, t2]).endMid ≠ hexConcreteR a h0 := by
  have hs : halfStep h0 ≠ 0 := hexConcrete_halfStep_ne h0
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
  
  · rw [hexConcrete_endMid_pp, hexConcrete_q_canon, hexConcrete_r_canon]
    refine ⟨?_, ?_, ?_⟩
    · conv_rhs => rw [hexConcrete_a_canon a h0]
      exact hexConcrete_mid_ne a (halfStep h0) hs 3 3 0 0 (by simp)
    · exact hexConcrete_mid_ne a (halfStep h0) hs 3 3 1 (-1) (by norm_num)
    · exact hexConcrete_mid_ne a (halfStep h0) hs 3 3 2 1 (by norm_num)
  
  · rw [hexConcrete_endMid_pm, hexConcrete_q_canon, hexConcrete_r_canon]
    refine ⟨?_, ?_, ?_⟩
    · conv_rhs => rw [hexConcrete_a_canon a h0]
      exact hexConcrete_mid_ne a (halfStep h0) hs 4 2 0 0 (by simp)
    · exact hexConcrete_mid_ne a (halfStep h0) hs 4 2 1 (-1) (by norm_num)
    · exact hexConcrete_mid_ne a (halfStep h0) hs 4 2 2 1 (by norm_num)
  
  · rw [hexConcrete_endMid_mp, hexConcrete_q_canon, hexConcrete_r_canon]
    refine ⟨?_, ?_, ?_⟩
    · conv_rhs => rw [hexConcrete_a_canon a h0]
      exact hexConcrete_mid_ne a (halfStep h0) hs 2 (-2) 0 0 (by norm_num)
    · exact hexConcrete_mid_ne a (halfStep h0) hs 2 (-2) 1 (-1) (by norm_num)
    · exact hexConcrete_mid_ne a (halfStep h0) hs 2 (-2) 2 1 (by norm_num)
  
  · rw [hexConcrete_endMid_mm, hexConcrete_q_canon, hexConcrete_r_canon]
    refine ⟨?_, ?_, ?_⟩
    · conv_rhs => rw [hexConcrete_a_canon a h0]
      exact hexConcrete_mid_ne a (halfStep h0) hs 0 (-3) 0 0 (by norm_num)
    · exact hexConcrete_mid_ne a (halfStep h0) hs 0 (-3) 1 (-1) (by norm_num)
    · exact hexConcrete_mid_ne a (halfStep h0) hs 0 (-3) 2 1 (by norm_num)


end StatMech.Universality
