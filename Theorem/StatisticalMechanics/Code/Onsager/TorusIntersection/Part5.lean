/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Def.StatisticalMechanics.Code.Onsager.TorusIntersection.Part5


namespace StatMech.Onsager

open BigOperators StatMech.Ising

@[simp] theorem ons_zmodPrefix_zero
    {A : Type*} [AddCommMonoid A]
    {L : ℕ} [NeZero L] (f : ZMod L → A) :
    ons_zmodPrefix f 0 = 0 := by
  simp [ons_zmodPrefix]

theorem ons_zmodPrefix_add_one
    {A : Type*} [AddCommMonoid A]
    {L : ℕ} [Fact (2 < L)] (f : ZMod L → A)
    (z : ZMod L) (hz : z ≠ -1) :
    ons_zmodPrefix f (z + 1) = ons_zmodPrefix f z + f (z + 1) := by
  letI : Fact (1 < L) := ⟨by
    have := (Fact.out : 2 < L)
    omega⟩
  have hv : z.val + 1 < L := by
    have hne : z.val ≠ L - 1 := by
      intro h
      apply hz
      apply ZMod.val_injective L
      rw [h, ons_zmod_val_neg_one]
    have := z.val_lt
    omega
  have hval : (z + 1).val = z.val + 1 := by
    rw [ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt hv]
  have hcast : (((z.val + 1 : ℕ) : ZMod L)) = z + 1 := by
    apply ZMod.val_injective L
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hv, hval]
  unfold ons_zmodPrefix
  rw [hval, Finset.sum_range_succ, hcast]

theorem ons_zmodPrefix_eq_add_pred
    {A : Type*} [AddCommMonoid A]
    {L : ℕ} [Fact (2 < L)] (f : ZMod L → A)
    (z : ZMod L) (hz : z ≠ 0) :
    ons_zmodPrefix f z = ons_zmodPrefix f (z - 1) + f z := by
  have hpred : z - 1 ≠ -1 := by
    intro h
    apply hz
    calc
      z = (z - 1) + 1 := by ring
      _ = -1 + 1 := by rw [h]
      _ = 0 := by ring
  simpa only [sub_add_cancel] using
    ons_zmodPrefix_add_one f (z - 1) hpred

theorem ons_zmodPrefix_neg_one_of_sum_zero
    {L : ℕ} [Fact (2 < L)] (f : ZMod L → ZMod 2)
    (hsum : ∑ z, f z = 0) :
    ons_zmodPrefix f (-1) = f 0 := by
  have hL : L = (L - 1) + 1 := by
    have := (Fact.out : 2 < L)
    omega
  have hrange := ons_sum_zmod_eq_sum_range L f
  have hdecomp :
      (∑ i ∈ Finset.range L, f (i : ZMod L)) =
        f 0 + ∑ i ∈ Finset.range (L - 1),
          f ((i + 1 : ℕ) : ZMod L) := by
    have hrangeEq : Finset.range L = Finset.range ((L - 1) + 1) := by
      exact congrArg Finset.range hL
    rw [hrangeEq]
    simpa only [Nat.cast_zero] using
      ons_sum_range_succ_first (fun i : ℕ => f (i : ZMod L)) (L - 1)
  rw [hdecomp] at hrange
  have hprefix :
      (∑ i ∈ Finset.range (L - 1), f (↑(i + 1) : ZMod L)) =
        ons_zmodPrefix f (-1) := by
    unfold ons_zmodPrefix
    rw [ons_zmod_val_neg_one]
  rw [hprefix] at hrange
  rw [hsum] at hrange
  have hzero : f 0 + ons_zmodPrefix f (-1) = 0 := hrange.symm
  exact (eq_neg_of_add_eq_zero_right hzero).trans (CharTwo.neg_eq _)

theorem ons_zmod_eq_neg_one_of_eq_pred
    {A : Type*} {L : ℕ} [Fact (2 < L)]
    (f : ZMod L → A) (hpred : ∀ z, f z = f (z - 1))
    (z : ZMod L) :
    f z = f (-1) := by
  have hnat : ∀ n : ℕ, n < L → f (n : ZMod L) = f 0 := by
    intro n hn
    induction n with
    | zero => simp only [Nat.cast_zero]
    | succ n ih =>
        have hstep := hpred ((n + 1 : ℕ) : ZMod L)
        have hsub : (((n + 1 : ℕ) : ZMod L) - 1) = (n : ZMod L) := by
          rw [Nat.cast_add, Nat.cast_one]
          ring
        rw [hsub] at hstep
        exact hstep.trans (ih (by omega))
  calc
    f z = f (z.val : ZMod L) := by rw [ZMod.natCast_zmod_val]
    _ = f 0 := hnat z.val z.val_lt
    _ = f (-1) := by simpa only [zero_sub] using hpred 0

theorem ons_xFlux_eq_neg_one
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (x : ZMod L) :
    ons_xFlux F x = ons_xFlux F (-1) := by
  exact ons_zmod_eq_neg_one_of_eq_pred
    (ons_xFlux F) (ons_xFlux_pred L F hF) x

theorem ons_yFlux_eq_neg_one
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (y : ZMod L) :
    ons_yFlux F y = ons_yFlux F (-1) := by
  exact ons_zmod_eq_neg_one_of_eq_pred
    (ons_yFlux F) (ons_yFlux_pred L F hF) y

theorem ons_zmodPrefix_add_pred_of_sum_zero
    {L : ℕ} [Fact (2 < L)] (f : ZMod L → ZMod 2)
    (hsum : ∑ z, f z = 0) (z : ZMod L) :
    ons_zmodPrefix f z + ons_zmodPrefix f (z - 1) = f z := by
  by_cases hz : z = 0
  · subst z
    rw [zero_sub, ons_zmodPrefix_zero,
      ons_zmodPrefix_neg_one_of_sum_zero f hsum, zero_add]
  · rw [ons_zmodPrefix_eq_add_pred f z hz]
    calc
      (ons_zmodPrefix f (z - 1) + f z) +
          ons_zmodPrefix f (z - 1) =
          (ons_zmodPrefix f (z - 1) +
            ons_zmodPrefix f (z - 1)) + f z := by abel
      _ = f z := by rw [CharTwo.add_self_eq_zero, zero_add]

end StatMech.Onsager
