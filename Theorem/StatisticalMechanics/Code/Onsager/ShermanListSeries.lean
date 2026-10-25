/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanListSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLemma4Return.Part3


namespace StatMech.Onsager

open BigOperators

theorem summable_mul_prod {K : Type*} [RCLike K]
    {alpha beta : Type*} {f : alpha → K} {g : beta → K}
    (hf : Summable f) (hg : Summable g) :
    Summable (fun z : alpha × beta => f z.1 * g z.2) := by
  apply Summable.of_norm
  have hfn := hf.norm
  have hgn := hg.norm
  simp_rw [norm_mul]
  rw [summable_prod_of_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  constructor
  · intro a
    exact hgn.mul_left ‖f a‖
  · simp_rw [tsum_mul_left]
    exact hfn.mul_right (∑' b, ‖g b‖)


theorem ons_summable_tupleProd {K : Type*} [RCLike K]
    {alpha : Type*} (wt : alpha → K)
    (hwt : Summable wt) (k : ℕ) :
    Summable (fun p : Fin k → alpha => ∏ i, wt (p i)) := by
  induction k with
  | zero =>
      letI : Finite (Fin 0 → alpha) := Finite.of_subsingleton
      letI : Fintype (Fin 0 → alpha) := Fintype.ofFinite _
      exact (hasSum_fintype _).summable
  | succ k ih =>
      let split : (Fin (k + 1) → alpha) ≃ alpha × (Fin k → alpha) :=
        (Fin.consEquiv (fun _ : Fin (k + 1) => alpha)).symm
      have hp := summable_mul_prod hwt ih
      have hs := (split.summable_iff).mpr hp
      simpa [split, Fin.prod_univ_succ] using hs


theorem ons_tsum_tupleProd_eq_pow {K : Type*} [RCLike K]
    {alpha : Type*} (wt : alpha → K)
    (hwt : Summable wt) (k : ℕ) :
    (∑' p : Fin k → alpha, ∏ i, wt (p i)) = (∑' a, wt a) ^ k := by
  induction k with
  | zero =>
      letI : Finite (Fin 0 → alpha) := Finite.of_subsingleton
      letI : Fintype (Fin 0 → alpha) := Fintype.ofFinite _
      simp [tsum_fintype]
  | succ k ih =>
      let split : (Fin (k + 1) → alpha) ≃ alpha × (Fin k → alpha) :=
        (Fin.consEquiv (fun _ : Fin (k + 1) => alpha)).symm
      let f : alpha × (Fin k → alpha) → K :=
        fun z => wt z.1 * ∏ i, wt (z.2 i)
      have hfun : (fun p : Fin (k + 1) → alpha => ∏ i, wt (p i)) = f ∘ split := by
        funext p
        simp only [f, split, Function.comp_apply, Fin.consEquiv_symm_apply,
          Fin.prod_univ_succ]
        congr 1
      rw [hfun]
      calc
        (∑' p : Fin (k + 1) → alpha, (f ∘ split) p) = ∑' z, f z :=
          split.tsum_eq f
        _ = (∑' a, wt a) * (∑' p : Fin k → alpha, ∏ i, wt (p i)) := by
          rw [(summable_mul_prod hwt (ons_summable_tupleProd wt hwt k)).tsum_prod]
          simp only [Prod.fst, Prod.snd]
          simp_rw [tsum_mul_left]
          rw [tsum_mul_right]
        _ = (∑' a, wt a) ^ (k + 1) := by rw [ih, pow_succ, mul_comm]

end StatMech.Onsager
