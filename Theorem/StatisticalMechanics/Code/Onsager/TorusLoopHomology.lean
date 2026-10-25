/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.DecorationSum.Part4
import Theorem.StatisticalMechanics.Code.Onsager.TorusLoopCharacter.Part2
import Def.StatisticalMechanics.Code.Onsager.TorusLoopHomology.Part2


namespace StatMech.Onsager

open BigOperators StatMech.Ising

theorem ons_zmod_val_neg_one (L : ℕ) [NeZero L] :
    (-1 : ZMod L).val = L - 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne L)
  rw [ZMod.val_neg_one]
  omega

theorem ons_dirExponentX_eq_val_diff_add_wrap
    {L : ℕ} [Fact (2 < L)] (d : ons_Dart L) :
    ons_dirExponentX d.2 =
      (((ons_dirStep L d.2 d.1).1.val : ℕ) : ℤ) -
        ((d.1.1.val : ℕ) : ℤ) + (L : ℤ) * ons_xWrapSign d := by
  letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  have hL : 1 ≤ L := by have := (Fact.out : 2 < L); omega
  rcases d with ⟨p, mu⟩
  fin_cases mu
  · change (1 : ℤ) = (((p.1 + 1).val : ℕ) : ℤ) -
      ((p.1.val : ℕ) : ℤ) + (L : ℤ) * ons_xWrapSign (p, 0)
    by_cases hp : p.1 = -1
    · have hv : p.1.val = L - 1 := by rw [hp, ons_zmod_val_neg_one]
      have hh : (p.1 + 1).val = 0 := by rw [hp]; simp
      rw [hv, hh]
      simp [ons_xWrapSign, hp]
      rw [Nat.cast_sub hL]
      push_cast
      ring
    · have hv : p.1.val + 1 < L := by
        have hlt := ZMod.val_lt p.1
        have hne : p.1.val ≠ L - 1 := by
          intro h
          apply hp
          apply ZMod.val_injective
          rw [h, ons_zmod_val_neg_one]
        omega
      rw [ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt hv]
      simp [ons_xWrapSign, hp]
  · simp [ons_dirExponentX, ons_dirStep, ons_xWrapSign]
  · change (-1 : ℤ) = (((p.1 - 1).val : ℕ) : ℤ) -
      ((p.1.val : ℕ) : ℤ) + (L : ℤ) * ons_xWrapSign (p, 2)
    by_cases hp : p.1 = 0
    · have hv : p.1.val = 0 := by rw [hp]; exact ZMod.val_zero
      have hh : (p.1 - 1).val = L - 1 := by
        rw [hp, zero_sub, ons_zmod_val_neg_one]
      rw [hv, hh]
      simp [ons_xWrapSign, hp]
      rw [Nat.cast_sub hL]
      push_cast
      ring
    · have hpval : p.1.val ≠ 0 := by
        intro h
        apply hp
        exact (ZMod.val_eq_zero p.1).mp h
      have hone : (1 : ZMod L).val ≤ p.1.val := by
        rw [ZMod.val_one]
        omega
      rw [ZMod.val_sub hone, ZMod.val_one]
      simp [ons_xWrapSign, hp]
  · simp [ons_dirExponentX, ons_dirStep, ons_xWrapSign]

theorem ons_dirExponentY_eq_val_diff_add_wrap
    {L : ℕ} [Fact (2 < L)] (d : ons_Dart L) :
    ons_dirExponentY d.2 =
      (((ons_dirStep L d.2 d.1).2.val : ℕ) : ℤ) -
        ((d.1.2.val : ℕ) : ℤ) + (L : ℤ) * ons_yWrapSign d := by
  letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  have hL : 1 ≤ L := by have := (Fact.out : 2 < L); omega
  rcases d with ⟨p, mu⟩
  fin_cases mu
  · simp [ons_dirExponentY, ons_dirStep, ons_yWrapSign]
  · change (1 : ℤ) = (((p.2 + 1).val : ℕ) : ℤ) -
      ((p.2.val : ℕ) : ℤ) + (L : ℤ) * ons_yWrapSign (p, 1)
    by_cases hp : p.2 = -1
    · have hv : p.2.val = L - 1 := by rw [hp, ons_zmod_val_neg_one]
      have hh : (p.2 + 1).val = 0 := by rw [hp]; simp
      rw [hv, hh]
      simp [ons_yWrapSign, hp]
      rw [Nat.cast_sub hL]
      push_cast
      ring
    · have hv : p.2.val + 1 < L := by
        have hlt := ZMod.val_lt p.2
        have hne : p.2.val ≠ L - 1 := by
          intro h
          apply hp
          apply ZMod.val_injective
          rw [h, ons_zmod_val_neg_one]
        omega
      rw [ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt hv]
      simp [ons_yWrapSign, hp]
  · simp [ons_dirExponentY, ons_dirStep, ons_yWrapSign]
  · change (-1 : ℤ) = (((p.2 - 1).val : ℕ) : ℤ) -
      ((p.2.val : ℕ) : ℤ) + (L : ℤ) * ons_yWrapSign (p, 3)
    by_cases hp : p.2 = 0
    · have hv : p.2.val = 0 := by rw [hp]; exact ZMod.val_zero
      have hh : (p.2 - 1).val = L - 1 := by
        rw [hp, zero_sub, ons_zmod_val_neg_one]
      rw [hv, hh]
      simp [ons_yWrapSign, hp]
      rw [Nat.cast_sub hL]
      push_cast
      ring
    · have hpval : p.2.val ≠ 0 := by
        intro h
        apply hp
        exact (ZMod.val_eq_zero p.2).mp h
      have hone : (1 : ZMod L).val ≤ p.2.val := by
        rw [ZMod.val_one]
        omega
      rw [ZMod.val_sub hone, ZMod.val_one]
      simp [ons_yWrapSign, hp]

theorem ons_sum_dirExponentX_eq_wrap
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    (∑ k, ons_dirExponentX (d k).2) =
      (L : ℤ) * ∑ k, ons_xWrapSign (d k) := by
  have hhead :
      (∑ k, ((((ons_dirStep L (d k).2 (d k).1).1.val : ℕ) : ℤ))) =
        ∑ k, (((d k).1.1.val : ℕ) : ℤ) := by
    calc
      (∑ k, ((((ons_dirStep L (d k).2 (d k).1).1.val : ℕ) : ℤ))) =
          ∑ k, (((d (k - 1)).1.1.val : ℕ) : ℤ) := by
        apply Finset.sum_congr rfl
        intro k _
        have hk : k - 1 + 1 = k := by abel
        have h := hvalid (k - 1)
        rw [hk] at h
        rw [h]
      _ = ∑ k, (((d k).1.1.val : ℕ) : ℤ) :=
        by simpa [sub_eq_add_neg] using
          (Equiv.sum_comp (Equiv.addRight (-1 : Fin n))
            (fun k => (((d k).1.1.val : ℕ) : ℤ)))
  calc
    (∑ k, ons_dirExponentX (d k).2) =
        ∑ k, ((((ons_dirStep L (d k).2 (d k).1).1.val : ℕ) : ℤ) -
          (((d k).1.1.val : ℕ) : ℤ) + (L : ℤ) * ons_xWrapSign (d k)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact ons_dirExponentX_eq_val_diff_add_wrap (d k)
    _ = ((∑ k, (((ons_dirStep L (d k).2 (d k).1).1.val : ℕ) : ℤ)) -
          ∑ k, (((d k).1.1.val : ℕ) : ℤ)) +
        ∑ k, (L : ℤ) * ons_xWrapSign (d k) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (L : ℤ) * ∑ k, ons_xWrapSign (d k) := by
      rw [hhead, sub_self, zero_add, Finset.mul_sum]

theorem ons_sum_dirExponentY_eq_wrap
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    (∑ k, ons_dirExponentY (d k).2) =
      (L : ℤ) * ∑ k, ons_yWrapSign (d k) := by
  have hhead :
      (∑ k, ((((ons_dirStep L (d k).2 (d k).1).2.val : ℕ) : ℤ))) =
        ∑ k, (((d k).1.2.val : ℕ) : ℤ) := by
    calc
      (∑ k, ((((ons_dirStep L (d k).2 (d k).1).2.val : ℕ) : ℤ))) =
          ∑ k, (((d (k - 1)).1.2.val : ℕ) : ℤ) := by
        apply Finset.sum_congr rfl
        intro k _
        have hk : k - 1 + 1 = k := by abel
        have h := hvalid (k - 1)
        rw [hk] at h
        rw [h]
      _ = ∑ k, (((d k).1.2.val : ℕ) : ℤ) :=
        by simpa [sub_eq_add_neg] using
          (Equiv.sum_comp (Equiv.addRight (-1 : Fin n))
            (fun k => (((d k).1.2.val : ℕ) : ℤ)))
  calc
    (∑ k, ons_dirExponentY (d k).2) =
        ∑ k, ((((ons_dirStep L (d k).2 (d k).1).2.val : ℕ) : ℤ) -
          (((d k).1.2.val : ℕ) : ℤ) + (L : ℤ) * ons_yWrapSign (d k)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact ons_dirExponentY_eq_val_diff_add_wrap (d k)
    _ = ((∑ k, (((ons_dirStep L (d k).2 (d k).1).2.val : ℕ) : ℤ)) -
          ∑ k, (((d k).1.2.val : ℕ) : ℤ)) +
        ∑ k, (L : ℤ) * ons_yWrapSign (d k) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (L : ℤ) * ∑ k, ons_yWrapSign (d k) := by
      rw [hhead, sub_self, zero_add, Finset.mul_sum]

theorem ons_two_ne_zero {L : ℕ} [Fact (2 < L)] :
    (2 : ZMod L) ≠ 0 := by
  rw [Ne, ← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
  have := (Fact.out : 2 < L)
  omega

theorem ons_xSeamEdge_portEdge_iff {L : ℕ} [Fact (2 < L)]
    (d : ons_Dart L) :
    ons_xSeamEdge L (ons_portEdge L d) ↔ ons_xWrap d := by
  rcases d with ⟨p, mu⟩
  fin_cases mu <;> simp only [ons_xWrap] <;> norm_num <;> simp
  · exact show ons_xSeamEdge L (ons_portEdge L (p, 0)) ↔ p.1 = -1 from by
      simp only [ons_xSeamEdge, ons_portEdge, ons_dirStep, Sym2.eq_iff,
        Prod.mk.injEq]
      constructor
      · rintro ⟨y, (⟨hp, hstep, -⟩ | ⟨hp, -, -⟩)⟩
        · have hx : p.1 = 0 := congrArg Prod.fst hp
          rw [hx] at hstep
          exfalso
          apply (ons_two_ne_zero (L := L))
          linear_combination hstep
        · simpa using congrArg Prod.fst hp
      · intro hp
        refine ⟨p.2, Or.inr ⟨Prod.ext hp rfl, ?_, rfl⟩⟩
        rw [hp]
        simp
  · exact show ¬ons_xSeamEdge L (ons_portEdge L (p, 1)) from by
      rintro ⟨y, heq⟩
      simp only [ons_portEdge, ons_dirStep, Sym2.eq_iff, Prod.mk.injEq] at heq
      rcases heq with (⟨hp, hm, -⟩ | ⟨hp, h0, -⟩)
      · have h0' : p.1 = 0 := congrArg Prod.fst hp
        rw [h0'] at hm
        have h1 : (1 : ZMod L) = 0 := neg_eq_zero.mp hm.symm
        apply ons_two_ne_zero (L := L)
        linear_combination 2 * h1
      · have hm' : p.1 = -1 := congrArg Prod.fst hp
        rw [h0] at hm'
        have h1 : (1 : ZMod L) = 0 := neg_eq_zero.mp hm'.symm
        apply ons_two_ne_zero (L := L)
        linear_combination 2 * h1
  · exact show ons_xSeamEdge L (ons_portEdge L (p, 2)) ↔ p.1 = 0 from by
      simp only [ons_xSeamEdge, ons_portEdge, ons_dirStep, Sym2.eq_iff,
        Prod.mk.injEq]
      constructor
      · rintro ⟨y, (⟨hp, -, -⟩ | ⟨hp, hstep, -⟩)⟩
        · simpa using congrArg Prod.fst hp
        · have hx : p.1 = -1 := congrArg Prod.fst hp
          rw [hx] at hstep
          exfalso
          apply (ons_two_ne_zero (L := L))
          linear_combination -hstep
      · intro hp
        refine ⟨p.2, Or.inl ⟨Prod.ext hp rfl, ?_, rfl⟩⟩
        rw [hp]
        simp
  · exact show ¬ons_xSeamEdge L (ons_portEdge L (p, 3)) from by
      rintro ⟨y, heq⟩
      simp only [ons_portEdge, ons_dirStep, Sym2.eq_iff, Prod.mk.injEq] at heq
      rcases heq with (⟨hp, hm, -⟩ | ⟨hp, h0, -⟩)
      · have h0' : p.1 = 0 := congrArg Prod.fst hp
        rw [h0'] at hm
        have h1 : (1 : ZMod L) = 0 := neg_eq_zero.mp hm.symm
        apply ons_two_ne_zero (L := L)
        linear_combination 2 * h1
      · have hm' : p.1 = -1 := congrArg Prod.fst hp
        rw [h0] at hm'
        have h1 : (1 : ZMod L) = 0 := neg_eq_zero.mp hm'.symm
        apply ons_two_ne_zero (L := L)
        linear_combination 2 * h1

theorem ons_ySeamEdge_portEdge_iff {L : ℕ} [Fact (2 < L)]
    (d : ons_Dart L) :
    ons_ySeamEdge L (ons_portEdge L d) ↔ ons_yWrap d := by
  rcases d with ⟨p, mu⟩
  fin_cases mu <;> simp only [ons_yWrap] <;> norm_num <;> simp
  · exact show ¬ons_ySeamEdge L (ons_portEdge L (p, 0)) from by
      rintro ⟨x, heq⟩
      simp only [ons_portEdge, ons_dirStep, Sym2.eq_iff, Prod.mk.injEq] at heq
      rcases heq with (⟨hp, -, hm⟩ | ⟨hp, -, h0⟩)
      · have h0' : p.2 = 0 := congrArg Prod.snd hp
        rw [h0'] at hm
        have h1 : (1 : ZMod L) = 0 := neg_eq_zero.mp hm.symm
        apply ons_two_ne_zero (L := L)
        linear_combination 2 * h1
      · have hm' : p.2 = -1 := congrArg Prod.snd hp
        rw [h0] at hm'
        have h1 : (1 : ZMod L) = 0 := neg_eq_zero.mp hm'.symm
        apply ons_two_ne_zero (L := L)
        linear_combination 2 * h1
  · exact show ons_ySeamEdge L (ons_portEdge L (p, 1)) ↔ p.2 = -1 from by
      simp only [ons_ySeamEdge, ons_portEdge, ons_dirStep, Sym2.eq_iff,
        Prod.mk.injEq]
      constructor
      · rintro ⟨x, (⟨hp, -, hstep⟩ | ⟨hp, -, -⟩)⟩
        · have hy : p.2 = 0 := congrArg Prod.snd hp
          rw [hy] at hstep
          exfalso
          apply (ons_two_ne_zero (L := L))
          linear_combination hstep
        · simpa using congrArg Prod.snd hp
      · intro hp
        refine ⟨p.1, Or.inr ⟨Prod.ext rfl hp, rfl, ?_⟩⟩
        rw [hp]
        simp
  · exact show ¬ons_ySeamEdge L (ons_portEdge L (p, 2)) from by
      rintro ⟨x, heq⟩
      simp only [ons_portEdge, ons_dirStep, Sym2.eq_iff, Prod.mk.injEq] at heq
      rcases heq with (⟨hp, -, hm⟩ | ⟨hp, -, h0⟩)
      · have h0' : p.2 = 0 := congrArg Prod.snd hp
        rw [h0'] at hm
        have h1 : (1 : ZMod L) = 0 := neg_eq_zero.mp hm.symm
        apply ons_two_ne_zero (L := L)
        linear_combination 2 * h1
      · have hm' : p.2 = -1 := congrArg Prod.snd hp
        rw [h0] at hm'
        have h1 : (1 : ZMod L) = 0 := neg_eq_zero.mp hm'.symm
        apply ons_two_ne_zero (L := L)
        linear_combination 2 * h1
  · exact show ons_ySeamEdge L (ons_portEdge L (p, 3)) ↔ p.2 = 0 from by
      simp only [ons_ySeamEdge, ons_portEdge, ons_dirStep, Sym2.eq_iff,
        Prod.mk.injEq]
      constructor
      · rintro ⟨x, (⟨hp, -, -⟩ | ⟨hp, -, hstep⟩)⟩
        · simpa using congrArg Prod.snd hp
        · have hy : p.2 = -1 := congrArg Prod.snd hp
          rw [hy] at hstep
          exfalso
          apply (ons_two_ne_zero (L := L))
          linear_combination -hstep
      · intro hp
        refine ⟨p.1, Or.inl ⟨Prod.ext rfl hp, rfl, ?_⟩⟩
        rw [hp]
        simp

end StatMech.Onsager
