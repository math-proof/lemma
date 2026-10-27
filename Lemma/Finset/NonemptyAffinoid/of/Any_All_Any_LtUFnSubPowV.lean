import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.CerednikDrinfeld.DrinfeldHolomorphic


namespace Definitions
end Definitions
open Definitions
open CerednikDrinfeld.Omega


/--
[CerednikDrinfeld_Omega_affinoid_nonempty_of_exists_finset_cover](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_Omega_affinoid_nonempty_of_exists_finset_cover.lean)
-/

@[path]
private lemma main
  [Field K₀] [Field K] [Algebra K₀ K] [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
  {ϖ : PseudoUniformizer K₀ K}
  {n : ℕ}
-- given
  (hfin : ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n → ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n) :
-- imply
  (affinoid ϖ n).Nonempty := by
-- proof
  classical
  obtain ⟨T, hT⟩ := hfin
  set p := Valued.v (algebraMap K₀ K ϖ.ϖ) with hp
  have hp0 : 0 < p := ϖ.pos
  have hp1 : p ≤ 1 := ϖ.lt_one.le
  have hpn1 : p ^ n ≤ 1 := pow_le_one₀ zero_le hp1
  have hpinv : (1 : Γ₀) ≤ p⁻¹ ^ n := one_le_pow₀ ((one_le_inv₀ hp0).2 hp1)
  have exists_v_le_one_forall_v_sub_eq_one :
    ∀ (S : Finset K), (∀ s ∈ S, Valued.v s ≤ 1) →
      ∃ y : K, Valued.v y ≤ 1 ∧ ∀ s ∈ S, Valued.v (y - s) = 1 := by
    intro S hS
    if hS0 : S = ∅ then
      exact ⟨0, (Valuation.map_zero (Valued.v : Valuation K Γ₀)).symm ▸ zero_le, by simp [hS0]⟩
    else
      have hcard : S.card ≠ 0 := by rwa [ne_eq, Finset.card_eq_zero]
      set Q : Polynomial K := (∏ s ∈ S, (Polynomial.X - Polynomial.C s)) + 1 with hQ
      have hmonic : (∏ s ∈ S, (Polynomial.X - Polynomial.C s)).Monic :=
        Polynomial.monic_prod_of_monic _ _ fun s _ => Polynomial.monic_X_sub_C s
      have hdegP : (∏ s ∈ S, (Polynomial.X - Polynomial.C s)).natDegree = S.card := by
        rw [Polynomial.natDegree_prod_of_monic _ _ fun s _ => Polynomial.monic_X_sub_C s]
        simp
      have hdeg_lt_one :
        (1 : Polynomial K).degree < (∏ s ∈ S, (Polynomial.X - Polynomial.C s)).degree := by
        rw [Polynomial.degree_one, Polynomial.degree_eq_natDegree hmonic.ne_zero, hdegP]
        exact_mod_cast Nat.pos_of_ne_zero hcard
      have hQdeg : Q.degree ≠ 0 := by
        have hQmonic : Q.Monic := hmonic.add_of_left hdeg_lt_one
        rw [Polynomial.degree_eq_natDegree hQmonic.ne_zero]
        have : Q.natDegree = S.card := by
          rw [hQ, Polynomial.natDegree_add_eq_left_of_degree_lt hdeg_lt_one, hdegP]
        rw [this]
        exact_mod_cast hcard
      obtain ⟨y, hy⟩ := IsAlgClosed.exists_root Q hQdeg
      have hprod : ∏ s ∈ S, (y - s) = -1 := by
        have : Polynomial.eval y Q = 0 := hy
        rw [hQ, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_prod] at this
        simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at this
        exact eq_neg_of_add_eq_zero_left this
      have hvprod : ∏ s ∈ S, Valued.v (y - s) = 1 := by
        rw [← map_prod (Valued.v : Valuation K Γ₀), hprod, Valuation.map_neg, Valuation.map_one]
      have hy1 : Valued.v y ≤ 1 := by
        by_contra hlt
        push Not at hlt
        have heach : ∀ s ∈ S, Valued.v (y - s) = Valued.v y := by
          intro s hs
          rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left]
          rw [Valuation.map_neg]
          exact (hS s hs).trans_lt hlt
        rw [Finset.prod_congr rfl heach, Finset.prod_const] at hvprod
        exact (one_lt_pow₀ hlt hcard).ne' hvprod
      refine ⟨y, hy1, fun s₀ hs₀ => ?_⟩
      have hle : ∀ s ∈ S, Valued.v (y - s) ≤ 1 := fun s hs =>
        (Valuation.map_sub _ _ _).trans (max_le hy1 (hS s hs))
      by_contra hne
      have hlt : Valued.v (y - s₀) < 1 := lt_of_le_of_ne (hle s₀ hs₀) hne
      have : ∏ s ∈ S, Valued.v (y - s) < 1 := by
        rw [← Finset.mul_prod_erase S _ hs₀]
        calc
          _ ≤ Valued.v (y - s₀) * 1 := by
            gcongr
            exact Finset.prod_le_one fun s hs => hle s (Finset.mem_of_mem_erase hs)
          _ < 1 := by rwa [mul_one]
      exact this.ne hvprod
  have hS_le : ∀ s ∈ (T.filter fun t => Valued.v (algebraMap K₀ K t) ≤ 1).image (algebraMap K₀ K),
      Valued.v s ≤ 1 := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    exact (Finset.mem_filter.mp ht).2
  obtain ⟨z, hz1, hzS⟩ := exists_v_le_one_forall_v_sub_eq_one
    ((T.filter fun t => Valued.v (algebraMap K₀ K t) ≤ 1).image (algebraMap K₀ K)) hS_le
  have hzt : ∀ t ∈ T, 1 ≤ Valued.v (z - algebraMap K₀ K t) := by
    intro t ht
    if h1 : Valued.v (algebraMap K₀ K t) ≤ 1 then
      exact (hzS _ (Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, h1⟩, rfl⟩)).ge
    else
      push Not at h1
      rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_right, Valuation.map_neg]
      · exact h1.le
      ·
        rw [Valuation.map_neg]
        exact hz1.trans_lt h1
  refine ⟨z, hz1.trans hpinv, fun a ha => ?_⟩
  obtain ⟨t, ht, hat⟩ := hT a ha
  have hlt : Valued.v (algebraMap K₀ K t - algebraMap K₀ K a) < Valued.v (z - algebraMap K₀ K t) := by
    rw [← Valuation.map_neg, neg_sub] at hat
    rw [← neg_sub, Valuation.map_neg]
    rw [← neg_sub, Valuation.map_neg] at hat
    exact hat.trans_le (hpn1.trans (hzt t ht))
  have heq : z - algebraMap K₀ K a = (z - algebraMap K₀ K t) + (algebraMap K₀ K t - algebraMap K₀ K a) := by
    ring
  rw [heq, Valuation.map_add_eq_of_lt_left _ hlt]
  exact hpn1.trans (hzt t ht)


-- created on 2026-10-24
