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
open Finset Filter Topology

/-!
# Gauss summation specialized to Frisch's binomial identity
-/


namespace MetaMathlibExt

section

theorem poch_prod (s : ℝ) (k : ℕ) :
    (ascPochhammer ℝ (k + 1)).eval s = ∏ j ∈ Finset.range (k + 1), (s + (j : ℝ)) := by
  induction k with
  | zero =>
    rw [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty]
    simp [ascPochhammer_one]
  | succ k ih =>
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    have h1 : (ascPochhammer ℝ (k + 1 + 1)).eval s
        = (ascPochhammer ℝ (k + 1)).eval s * (s + ((k + 1 : ℕ) : ℝ)) :=
      ascPochhammer_succ_eval (k + 1) s
    rw [h1, ih, hcast]
    conv_rhs => rw [Finset.prod_range_succ, hcast]

theorem poch_one (k : ℕ) :
    (ascPochhammer ℝ k).eval (1 : ℝ) = (Nat.factorial k : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, ih]
    rw [Nat.factorial_succ]
    push_cast
    ring

theorem poch_ratio (m k : ℕ) (hm : 1 ≤ m) :
    (ascPochhammer ℝ k).eval (((m + 1 : ℕ)) : ℝ)
      = (((m : ℝ) + (k : ℝ)) / (m : ℝ)) * (ascPochhammer ℝ k).eval (m : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
    exact ne_of_gt this
  induction k with
  | zero => simp [hm0]
  | succ k ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, ih]
    push_cast
    field_simp
    ring

theorem poch_nat_le (m k : ℕ) (hm : 1 ≤ m) :
    (ascPochhammer ℝ k).eval (m : ℝ) / (Nat.factorial k : ℝ)
      ≤ ((k : ℝ) + 1) ^ ((m : ℝ) - 1) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  suffices h : ∀ p : ℕ, 1 ≤ p →
      (ascPochhammer ℝ k).eval (p : ℝ) / (Nat.factorial k : ℝ)
        ≤ ((k : ℝ) + 1) ^ ((p : ℝ) - 1) from h m hm
  intro p
  induction p with
  | zero => intro hcon; omega
  | succ p ih =>
    intro hp1
    by_cases hp0 : p = 0
    · subst hp0
      have h1 : ((((0 + 1 : ℕ))) : ℝ) = (1 : ℝ) := by norm_cast
      rw [h1, poch_one]
      have hfact : (Nat.factorial k : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
      rw [div_self hfact]
      simp
    · have hpp : 1 ≤ p := by omega
      have ih' := ih hpp
      have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
      have hpos : 0 < (ascPochhammer ℝ k).eval (p : ℝ) := by
        apply ascPochhammer_pos
        exact_mod_cast (by omega : 0 < p)
      have hfactpos : (0 : ℝ) < (Nat.factorial k : ℝ) := by
        exact_mod_cast Nat.factorial_pos k
      have hY0 : (0 : ℝ) ≤ (ascPochhammer ℝ k).eval (p : ℝ) / (Nat.factorial k : ℝ) :=
        div_nonneg hpos.le hfactpos.le
      have hk1pos : (0 : ℝ) < (k : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      have hstep : ((p : ℝ) + (k : ℝ)) / (p : ℝ) ≤ (k : ℝ) + 1 := by
        have hmk : (k : ℝ) ≤ (p : ℝ) * (k : ℝ) := by
          have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp
          calc (k : ℝ) = 1 * (k : ℝ) := by ring
            _ ≤ (p : ℝ) * (k : ℝ) :=
              mul_le_mul_of_nonneg_right hp1R (Nat.cast_nonneg k)
        rw [div_le_iff₀ hpR]
        linarith
      have hexp : ((((p + 1 : ℕ))) : ℝ) - 1 = ((p : ℝ) - 1) + 1 := by
        push_cast; ring
      have hpcast : ((((p + 1 : ℕ))) : ℝ) = (p : ℝ) + 1 := by push_cast; ring
      have hrat := poch_ratio p k (by omega : 1 ≤ p)
      have hrw : (ascPochhammer ℝ k).eval (((p + 1 : ℕ) : ℝ)) / (Nat.factorial k : ℝ)
          = (((p : ℝ) + (k : ℝ)) / (p : ℝ))
            * ((ascPochhammer ℝ k).eval (p : ℝ) / (Nat.factorial k : ℝ)) := by
        rw [hpcast] at hrat ⊢
        rw [hrat]; ring
      rw [hrw, hexp, Real.rpow_add hk1pos]
      simp only [Real.rpow_one]
      calc (((p : ℝ) + (k : ℝ)) / (p : ℝ))
            * ((ascPochhammer ℝ k).eval (p : ℝ) / (Nat.factorial k : ℝ))
          ≤ ((k : ℝ) + 1) * ((ascPochhammer ℝ k).eval (p : ℝ) / (Nat.factorial k : ℝ)) :=
            mul_le_mul_of_nonneg_right hstep hY0
        _ ≤ ((k : ℝ) + 1) * (((k : ℝ) + 1) ^ ((p : ℝ) - 1)) :=
            mul_le_mul_of_nonneg_left ih' hk1pos.le
        _ = ((k : ℝ) + 1) ^ ((p : ℝ) - 1) * ((k : ℝ) + 1) := by ring

theorem poch_ratio_rpow_bound (A C c : ℝ) (hA : A = C - c) (hC : 0 < C) (_hc : 0 < c) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ k : ℕ in atTop,
      |(ascPochhammer ℝ (k + 1)).eval A / (ascPochhammer ℝ (k + 1)).eval C|
        ≤ M * (k : ℝ) ^ (-c) := by
  have hCpos : ∀ k : ℕ, 0 < (ascPochhammer ℝ k).eval C :=
    fun k => ascPochhammer_pos k C hC
  by_cases hdeg : ∃ m0 : ℕ, A = -((m0 : ℕ) : ℝ)
  · obtain ⟨m0, hm0⟩ := hdeg
    refine ⟨1, one_pos, ?_⟩
    filter_upwards [eventually_ge_atTop m0] with k hk
    have hzero : (ascPochhammer ℝ (k + 1)).eval A = 0 := by
      rw [ascPochhammer_eval_eq_zero_iff]
      refine ⟨m0, by omega, by linarith⟩
    rw [hzero, zero_div, abs_zero]
    apply mul_nonneg zero_le_one
    exact Real.rpow_nonneg (Nat.cast_nonneg k) _
  · rw [not_exists] at hdeg
    have hGA : Real.Gamma A ≠ 0 := by
      apply Real.Gamma_ne_zero
      intro m
      exact hdeg m
    have hGC : Real.Gamma C ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos hC)
    have hlimC : Tendsto (Real.GammaSeq C) atTop (𝓝 (Real.Gamma C)) :=
      Real.GammaSeq_tendsto_Gamma C
    have hlimA : Tendsto (Real.GammaSeq A) atTop (𝓝 (Real.Gamma A)) :=
      Real.GammaSeq_tendsto_Gamma A
    have hlim : Tendsto (fun k : ℕ => Real.GammaSeq C k / Real.GammaSeq A k)
        atTop (𝓝 (Real.Gamma C / Real.Gamma A)) :=
      hlimC.div hlimA hGA
    refine ⟨‖Real.Gamma C / Real.Gamma A‖ + 1, by positivity, ?_⟩
    have hball := Metric.ball_mem_nhds (Real.Gamma C / Real.Gamma A) one_pos
    have hev0 := hlim.eventually hball
    have hGS : ∀ (s : ℝ) (k : ℕ), Real.GammaSeq s k
        = (k : ℝ) ^ s * (Nat.factorial k : ℝ) / (ascPochhammer ℝ (k + 1)).eval s := by
      intro s k
      unfold Real.GammaSeq
      rw [poch_prod]
    have hCeq : C = c + A := by linarith
    filter_upwards [eventually_ge_atTop 1, hev0] with k hk hmem
    have hkR : (0 : ℝ) < (k : ℝ) := by
      have : 0 < k := by omega
      exact_mod_cast this
    have hCk1 : (ascPochhammer ℝ (k + 1)).eval C ≠ 0 :=
      ne_of_gt (hCpos (k + 1))
    have hAk1 : (ascPochhammer ℝ (k + 1)).eval A ≠ 0 := by
      intro hcon
      rw [ascPochhammer_eval_eq_zero_iff] at hcon
      obtain ⟨j, _, hjA⟩ := hcon
      exact hdeg j (by linarith)
    have hfact : (Nat.factorial k : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hrA : (k : ℝ) ^ A ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hkR A)
    have hrC : (k : ℝ) ^ C ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hkR C)
    have hdist : dist (Real.GammaSeq C k / Real.GammaSeq A k)
        (Real.Gamma C / Real.Gamma A) < 1 := Metric.mem_ball.mp hmem
    have htri : ‖Real.GammaSeq C k / Real.GammaSeq A k‖
        ≤ ‖Real.Gamma C / Real.Gamma A‖ + 1 := by
      have h1 : ‖Real.GammaSeq C k / Real.GammaSeq A k‖
          ≤ ‖Real.GammaSeq C k / Real.GammaSeq A k - Real.Gamma C / Real.Gamma A‖
            + ‖Real.Gamma C / Real.Gamma A‖ := by
        have hle := norm_add_le
          (Real.GammaSeq C k / Real.GammaSeq A k - Real.Gamma C / Real.Gamma A)
          (Real.Gamma C / Real.Gamma A)
        rwa [sub_add_cancel] at hle
      have h2 : ‖Real.GammaSeq C k / Real.GammaSeq A k - Real.Gamma C / Real.Gamma A‖ < 1 := by
        rwa [← dist_eq_norm]
      linarith
    have hkc : (k : ℝ) ^ (-c) * (k : ℝ) ^ c = 1 := by
      rw [← Real.rpow_add hkR]
      simp
    have hratio : (ascPochhammer ℝ (k + 1)).eval A / (ascPochhammer ℝ (k + 1)).eval C
        = (k : ℝ) ^ (-c) * (Real.GammaSeq C k / Real.GammaSeq A k) := by
      rw [hGS C k, hGS A k, hCeq, Real.rpow_add hkR]
      field_simp
      rw [hkc]
    rw [hratio, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _)]
    have hnorm : |(Real.GammaSeq C k / Real.GammaSeq A k)|
        = ‖Real.GammaSeq C k / Real.GammaSeq A k‖ := (Real.norm_eq_abs _).symm
    rw [hnorm]
    calc (k : ℝ) ^ (-c) * ‖Real.GammaSeq C k / Real.GammaSeq A k‖
        ≤ (k : ℝ) ^ (-c) * (‖Real.Gamma C / Real.Gamma A‖ + 1) :=
          mul_le_mul_of_nonneg_left htri
            (Real.rpow_nonneg (Nat.cast_nonneg k) _)
      _ = (‖Real.Gamma C / Real.Gamma A‖ + 1) * (k : ℝ) ^ (-c) := by ring

end
end MetaMathlibExt
