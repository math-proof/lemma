/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexPairingMaps.Part4


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators


theorem hexConcrete_halfStep_sub (h : ℤ) : halfStep (h - 1) = -(hexOmega * halfStep h) := by
  unfold halfStep
  have key : hexUnit ((h - 1) + 3) = - hexUnit (h - 1) := hexUnit_add_three (h - 1)
  rw [show ((h - 1) + 3 : ℤ) = h + 2 by ring, hexUnit_add_two] at key
  linear_combination (1 / 2 : ℂ) * key


theorem hexConcrete_halfStep_add (h : ℤ) : halfStep (h + 1) = -(hexOmega ^ 2 * halfStep h) := by
  unfold halfStep
  have key : hexUnit ((h + 1) + 3) = - hexUnit (h + 1) := hexUnit_add_three (h + 1)
  rw [show ((h + 1) + 3 : ℤ) = h + 4 by ring, hexUnit_add_four] at key
  linear_combination (1 / 2 : ℂ) * key


theorem hexConcrete_halfStep_sub2 (h : ℤ) : halfStep (h - 2) = hexOmega ^ 2 * halfStep h := by
  rw [show (h - 2 : ℤ) = (h - 1) - 1 by ring, hexConcrete_halfStep_sub,
    hexConcrete_halfStep_sub]; ring


theorem hexConcrete_halfStep_add2 (h : ℤ) : halfStep (h + 2) = hexOmega * halfStep h := by
  rw [show (h + 2 : ℤ) = (h + 1) + 1 by ring, hexConcrete_halfStep_add,
    hexConcrete_halfStep_add]
  have h3 : hexOmega ^ 3 = 1 := hexOmega_primRoot.pow_eq_one
  linear_combination (hexOmega * halfStep h) * h3


theorem hexConcrete_halfStep_ne (h : ℤ) : halfStep h ≠ 0 := by
  unfold halfStep
  simp only [ne_eq, mul_eq_zero, not_or]
  exact ⟨by norm_num, hexUnit_ne_zero h⟩


theorem hexConcrete_du_ne (h0 : ℤ) : (-halfStep h0) ≠ 0 := by
  simp only [ne_eq, neg_eq_zero]; exact hexConcrete_halfStep_ne h0


theorem hexConcrete_omega_cubic : hexOmega ^ 2 = -hexOmega - 1 := by
  have h3 : hexOmega ^ 3 = 1 := hexOmega_primRoot.pow_eq_one
  have hne : hexOmega - 1 ≠ 0 := sub_ne_zero.mpr hexOmega_ne_one
  have factored : (hexOmega - 1) * (hexOmega ^ 2 + hexOmega + 1) = 0 := by
    ring_nf; linear_combination h3
  rcases mul_eq_zero.mp factored with h | h
  · exact absurd h hne
  · linear_combination h


theorem hexConcrete_omega_im_pos : 0 < hexOmega.im := by
  unfold hexOmega
  rw [Complex.exp_ofReal_mul_I_im]
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · have := Real.pi_pos; linarith


theorem hexConcrete_omega_lin_indep (α β : ℝ)
    (h : (α : ℂ) + (β : ℂ) * hexOmega = 0) : α = 0 ∧ β = 0 := by
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.zero_im, zero_add, zero_mul, add_zero] at him
  have hb : β = 0 := by
    rcases mul_eq_zero.mp him with h1 | h2
    · exact h1
    · exact absurd h2 (ne_of_gt hexConcrete_omega_im_pos)
  subst hb
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.zero_re, zero_mul, sub_zero, add_zero] at hre
  exact ⟨hre, rfl⟩


theorem hexConcrete_mid_ne (a s : ℂ) (hs : s ≠ 0) (α₁ β₁ α₂ β₂ : ℝ)
    (hne : ¬(α₁ = α₂ ∧ β₁ = β₂)) :
    a + ((α₁ : ℂ) + (β₁ : ℂ) * hexOmega) * s ≠ a + ((α₂ : ℂ) + (β₂ : ℂ) * hexOmega) * s := by
  intro heq
  apply hne
  have hd : ((α₁ : ℂ) + (β₁ : ℂ) * hexOmega) * s - ((α₂ : ℂ) + (β₂ : ℂ) * hexOmega) * s = 0 := by
    linear_combination heq
  have hfac : (((α₁ - α₂ : ℝ) : ℂ) + ((β₁ - β₂ : ℝ) : ℂ) * hexOmega) * s = 0 := by
    push_cast; linear_combination hd
  have hz : ((α₁ - α₂ : ℝ) : ℂ) + ((β₁ - β₂ : ℝ) : ℂ) * hexOmega = 0 := by
    rcases mul_eq_zero.mp hfac with h | h
    · exact h
    · exact absurd h hs
  obtain ⟨ha, hb⟩ := hexConcrete_omega_lin_indep _ _ hz
  exact ⟨by linarith [sub_eq_zero.mp ha], by linarith [sub_eq_zero.mp hb]⟩


theorem hexConcrete_mids_one (a : ℂ) (h t : ℤ) :
    (ofTurns a h [t]).mids = [a, a + halfStep h + halfStep (h + t)] := by
  unfold ofTurns HexWalk.mids; simp [midsAux]


theorem hexConcrete_endMid_one (a : ℂ) (h t : ℤ) :
    (ofTurns a h [t]).endMid = a + halfStep h + halfStep (h + t) := by
  unfold HexWalk.endMid ofTurns HexWalk.mids; simp [midsAux]


theorem hexConcrete_vertices_one (a : ℂ) (h t : ℤ) :
    (ofTurns a h [t]).vertices
      = [a + halfStep h, a + halfStep h + halfStep (h + t) + halfStep (h + t)] := by
  unfold ofTurns HexWalk.vertices; simp [verticesAux]


theorem hexConcrete_endMid_two (a : ℂ) (h t1 t2 : ℤ) :
    (ofTurns a h [t1, t2]).endMid
      = a + halfStep h + halfStep (h + t1) + halfStep (h + t1) + halfStep (h + t1 + t2) := by
  unfold HexWalk.endMid ofTurns HexWalk.mids; simp [midsAux]


theorem hexConcrete_saw_one (a : ℂ) (h t : ℤ) : (ofTurns a h [t]).IsSAW := by
  unfold HexWalk.IsSAW
  rw [hexConcrete_vertices_one, List.nodup_cons]
  refine ⟨?_, List.nodup_singleton _⟩
  simp only [List.mem_singleton]
  intro heq
  exact hexConcrete_halfStep_ne (h + t) (by linear_combination (1 / 2 : ℂ) * (heq.symm))


theorem hexConcrete_legalSAW_one (a : ℂ) (h t : ℤ) (ht : t = 1 ∨ t = -1) :
    (ofTurns a h [t]).IsLegalSAW := by
  refine ⟨?_, hexConcrete_saw_one a h t⟩
  intro s hs
  simp only [ofTurns_turns, List.mem_singleton] at hs
  rw [hs]; exact ht


end StatMech.Universality
