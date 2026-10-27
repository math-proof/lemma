import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.SpecialFunctions.GaussHypergeometricSummationFrisch.Part2
open Finset Filter Topology

/-!
# Gauss summation specialized to Frisch's binomial identity
-/


namespace MetaMathlibExt

section

theorem hasSum_tterm_zero (A C : ℝ) :
    HasSum (tterm A C 0) 1 := by
  have h0 : ∀ b' : ℕ, b' ≠ 0 → tterm A C 0 b' = 0 := by
    intro b' hb'
    rw [tterm]
    have hz : (ascPochhammer ℝ b').eval (0 : ℝ) = 0 := by
      rw [ascPochhammer_eval_zero]
      simp [hb']
    rw [hz, mul_zero, zero_div]
  have hH := hasSum_single (0 : ℕ) h0
  rwa [tterm_zero] at hH

theorem base_case (A C c : ℝ) : HasSum (tterm A C (((0 : ℕ)) : ℝ)) (Pprod C c 0) := by
  rw [Nat.cast_zero]
  have hP : Pprod C c 0 = 1 := by simp [Pprod]
  rw [hP]
  exact hasSum_tterm_zero A C

theorem step_case (A C c : ℝ) (hA : A = C - c) (hC : 0 < C) (hc : 0 < c)
    (n β : ℕ) (hnc : (n : ℝ) < c) (hβn : β + 1 ≤ n)
    (hIH : HasSum (tterm A C (β : ℝ)) (Pprod C c β)) :
    HasSum (tterm A C ((((β + 1 : ℕ))) : ℝ)) (Pprod C c (β + 1)) := by
  have hCne : ∀ k : ℕ, (ascPochhammer ℝ k).eval C ≠ 0 :=
    fun k => ne_of_gt (ascPochhammer_pos k C hC)
  have hs1 : Summable (tterm A C (β : ℝ)) :=
    summable_tterm A C c hA hC hc n β (by omega) hnc
  have hs2 : Summable (tterm A C ((((β + 1 : ℕ))) : ℝ)) :=
    summable_tterm A C c hA hC hc n (β + 1) hβn hnc
  have hβc : ((((β + 1 : ℕ))) : ℝ) = (β : ℝ) + 1 := by push_cast; ring
  have haPos : (0 : ℝ) < c - (β : ℝ) - 1 := by
    have hβnR : ((β : ℝ)) + 1 ≤ (n : ℝ) := by exact_mod_cast hβn
    linarith
  have haNe : (c - (β : ℝ) - 1) ≠ 0 := ne_of_gt haPos
  have hgsum : Summable (fun k : ℕ => (c - (β : ℝ) - 1) * tterm A C ((((β + 1 : ℕ))) : ℝ) k
      - (C - (β : ℝ) - 1) * tterm A C (β : ℝ) k) :=
    (hs2.mul_left _).sub (hs1.mul_left _)
  have htele : ∀ K : ℕ, (∑ i ∈ Finset.range K, ((c - (β : ℝ) - 1)
      * tterm A C ((((β + 1 : ℕ))) : ℝ) i - (C - (β : ℝ) - 1) * tterm A C (β : ℝ) i))
      = -(vterm A C (β : ℝ) K) := by
    intro K
    have h1 : (∑ i ∈ Finset.range K, ((c - (β : ℝ) - 1)
        * tterm A C ((((β + 1 : ℕ))) : ℝ) i - (C - (β : ℝ) - 1) * tterm A C (β : ℝ) i))
        = ∑ i ∈ Finset.range K, (vterm A C (β : ℝ) i - vterm A C (β : ℝ) (i + 1)) := by
      apply Finset.sum_congr rfl
      intro i _
      have hc := contiguous A C (β : ℝ) c hA hCne i
      rw [hβc]
      exact hc
    rw [h1, Finset.sum_range_sub', vterm_zero, zero_sub]
  have hlimR : Tendsto (fun K : ℕ => -(vterm A C (β : ℝ) K)) atTop (𝓝 0) := by
    have h := (tendsto_vterm A C c hA hC hc n β hβn hnc).neg
    rwa [neg_zero] at h
  have hSeq : (fun K : ℕ => ∑ i ∈ Finset.range K, ((c - (β : ℝ) - 1)
      * tterm A C ((((β + 1 : ℕ))) : ℝ) i - (C - (β : ℝ) - 1) * tterm A C (β : ℝ) i))
      = (fun K : ℕ => -(vterm A C (β : ℝ) K)) := funext htele
  have htsum0 : (∑' k : ℕ, ((c - (β : ℝ) - 1) * tterm A C ((((β + 1 : ℕ))) : ℝ) k
      - (C - (β : ℝ) - 1) * tterm A C (β : ℝ) k)) = 0 := by
    have hL := hgsum.hasSum.tendsto_sum_nat
    rw [hSeq] at hL
    exact tendsto_nhds_unique hL hlimR
  have hH2 : HasSum (fun k : ℕ => (c - (β : ℝ) - 1) * tterm A C ((((β + 1 : ℕ))) : ℝ) k
      - (C - (β : ℝ) - 1) * tterm A C (β : ℝ) k)
      ((c - (β : ℝ) - 1) * (∑' k : ℕ, tterm A C ((((β + 1 : ℕ))) : ℝ) k)
        - (C - (β : ℝ) - 1) * (Pprod C c β)) :=
    (hs2.hasSum.mul_left _).sub (hIH.mul_left _)
  have htsum_eq := hH2.tsum_eq
  rw [htsum0] at htsum_eq
  have hS : (∑' k : ℕ, tterm A C ((((β + 1 : ℕ))) : ℝ) k)
      = ((C - (β : ℝ) - 1) / (c - (β : ℝ) - 1)) * (Pprod C c β) := by
    have h1 : (c - (β : ℝ) - 1) * (∑' k : ℕ, tterm A C ((((β + 1 : ℕ))) : ℝ) k)
        = (C - (β : ℝ) - 1) * (Pprod C c β) := by linarith
    rw [div_mul_eq_mul_div, eq_div_iff haNe]
    linarith
  have hP : Pprod C c (β + 1)
      = ((C - (β : ℝ) - 1) / (c - (β : ℝ) - 1)) * (Pprod C c β) := by
    simp only [Pprod]
    rw [Finset.prod_range_succ]
    have e1 : C - (((β : ℕ) : ℝ) + 1) = C - (β : ℝ) - 1 := by ring
    have e2 : c - (((β : ℕ) : ℝ) + 1) = c - (β : ℝ) - 1 := by ring
    rw [e1, e2]
    exact mul_comm _ _
  have hfinal : (∑' k : ℕ, tterm A C ((((β + 1 : ℕ))) : ℝ) k) = Pprod C c (β + 1) := by
    rw [hS, hP]
  have hcon := hs2.hasSum
  rwa [hfinal] at hcon

theorem hasSum_tterm_prod (A C c : ℝ) (hA : A = C - c) (hC : 0 < C) (hc : 0 < c)
    (n : ℕ) (hnc : (n : ℝ) < c) (m : ℕ) (hmn : m ≤ n) :
    HasSum (tterm A C (m : ℝ)) (Pprod C c m) := by
  have key : ∀ m : ℕ, m ≤ n → HasSum (tterm A C (m : ℝ)) (Pprod C c m) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact base_case A C c
    | succ m ih =>
      intro hm
      exact step_case A C c hA hC hc n m hnc hm (ih (by omega))
  exact key m hmn

set_option linter.unusedVariables false in
/-- Gauss summation at the Frisch specialization: `₂F₁(1 + b - c, n; b + 1; 1)`
equals `Γ(c - n) Γ(b + 1) / (Γ(c) Γ(b - n + 1))` for `n ≥ 1`, `c > n`, and `b > -1`.

Source: Ulrich Abel, "A Short Proof of the Binomial Identities of Frisch and
Klamkin," Journal of Integer Sequences 23 (2020), Article 20.7.1, displayed
Frisch specialization at source lines 200-205 of the official TeX
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Abel/abel12.tex`.

Proves `Wanted` entry `gauss_hypergeometric_summation_frisch`.
-/
theorem gauss_hypergeometric_summation_frisch (n : ℕ) (hn : 1 ≤ n) (b c : ℝ)
    (hcn : (n : ℝ) < c) (hb : -1 < b) :
    ordinaryHypergeometric (1 + b - c) (n : ℝ) (b + 1) (1 : ℝ) =
      Real.Gamma (c - n) * Real.Gamma (b + 1) /
        (Real.Gamma c * Real.Gamma (b - n + 1)) := by
  have hCpos : (0 : ℝ) < b + 1 := by linarith
  have hcpos : (0 : ℝ) < c := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hAeq : (1 : ℝ) + b - c = (b + 1) - c := by ring
  have hLHS : ordinaryHypergeometric (1 + b - c) (n : ℝ) (b + 1) (1 : ℝ)
      = ∑' k : ℕ, tterm (1 + b - c) (b + 1) (n : ℝ) k := by
    have h := ordinaryHypergeometric_sum_eq (1 + b - c) ((n : ℝ)) (b + 1) (1 : ℝ)
    unfold ordinaryHypergeometric
    rw [h]
    apply tsum_congr
    intro k
    have hCk : (ascPochhammer ℝ k).eval (b + 1) ≠ 0 :=
      ne_of_gt (ascPochhammer_pos _ _ hCpos)
    have hfk : (Nat.factorial k : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    rw [tterm]
    simp only [one_pow, smul_eq_mul, mul_one]
    field_simp
  have hP := (hasSum_tterm_prod (1 + b - c) (b + 1) c hAeq hCpos hcpos n hcn n le_rfl).tsum_eq
  have hRHS : Real.Gamma (c - (n : ℝ)) * Real.Gamma (b + 1)
      / (Real.Gamma c * Real.Gamma (b - (n : ℝ) + 1)) = Pprod (b + 1) c n := by
    have h := rhs_eq_prod n b c hcn hb
    rw [h]
    simp only [Pprod]
    apply Finset.prod_congr rfl
    intro j _
    have e1 : (b : ℝ) + 1 - ((j : ℝ) + 1) = b - (j : ℝ) := by ring
    rw [e1]
  rw [hLHS, hP, hRHS]

end
end MetaMathlibExt
