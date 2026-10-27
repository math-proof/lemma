/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.SpecialFunctions.Part1Ch9Entry24Dougall
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry24Dougall

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

theorem dilogCos_term_eq (rho angle : ℝ) (j : ℕ) :
    chapter9DilogCosTerm rho angle j =
      rho ^ (j + 1) * Real.cos ((((j + 1 : ℕ)) : ℝ) * angle) /
        ((((j + 1 : ℕ)) : ℝ) ^ 2) := rfl

theorem dilogSin_term_eq (rho angle : ℝ) (j : ℕ) :
    chapter9DilogSinTerm rho angle j =
      rho ^ (j + 1) * Real.sin ((((j + 1 : ℕ)) : ℝ) * angle) /
        ((((j + 1 : ℕ)) : ℝ) ^ 2) := rfl

theorem summable_inv_succ_sq :
    Summable (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2)) := by
  have hz : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
    hasSum_zeta_two.summable
  have h := (summable_nat_add_iff 1).mpr hz
  simpa using h

theorem summable_dilogCosTerm (rho angle : ℝ) (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    Summable (chapter9DilogCosTerm rho angle) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) summable_inv_succ_sq
  rw [dilogCos_term_eq]
  have hD : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ) ^ 2) := by positivity
  have habs : |rho| ≤ 1 := abs_le.mpr ⟨by linarith, hrho1⟩
  have hpow : |rho ^ (j + 1)| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) habs
  have hcos : |Real.cos ((((j + 1 : ℕ)) : ℝ) * angle)| ≤ 1 :=
    Real.abs_cos_le_one _
  have hnum : |rho ^ (j + 1) * Real.cos ((((j + 1 : ℕ)) : ℝ) * angle)| ≤ 1 := by
    calc |rho ^ (j + 1) * Real.cos ((((j + 1 : ℕ)) : ℝ) * angle)|
          = |rho ^ (j + 1)| * |Real.cos ((((j + 1 : ℕ)) : ℝ) * angle)| :=
            abs_mul _ _
      _ ≤ 1 * 1 :=
          mul_le_mul hpow hcos (abs_nonneg _) (by norm_num)
      _ = 1 := mul_one 1
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hD]
  exact div_le_div_of_nonneg_right hnum (le_of_lt hD)

theorem summable_dilogSinTerm (rho angle : ℝ) (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    Summable (chapter9DilogSinTerm rho angle) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) summable_inv_succ_sq
  rw [dilogSin_term_eq]
  have hD : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ) ^ 2) := by positivity
  have habs : |rho| ≤ 1 := abs_le.mpr ⟨by linarith, hrho1⟩
  have hpow : |rho ^ (j + 1)| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) habs
  have hsin : |Real.sin ((((j + 1 : ℕ)) : ℝ) * angle)| ≤ 1 :=
    Real.abs_sin_le_one _
  have hnum : |rho ^ (j + 1) * Real.sin ((((j + 1 : ℕ)) : ℝ) * angle)| ≤ 1 := by
    calc |rho ^ (j + 1) * Real.sin ((((j + 1 : ℕ)) : ℝ) * angle)|
          = |rho ^ (j + 1)| * |Real.sin ((((j + 1 : ℕ)) : ℝ) * angle)| :=
            abs_mul _ _
      _ ≤ 1 * 1 :=
          mul_le_mul hpow hsin (abs_nonneg _) (by norm_num)
      _ = 1 := mul_one 1
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hD]
  exact div_le_div_of_nonneg_right hnum (le_of_lt hD)

theorem boundaryLog_zero : chapter9BoundaryLog 0 = 0 := by simp [chapter9BoundaryLog]

theorem boundaryLog_one : chapter9BoundaryLog 1 = 0 := by simp [chapter9BoundaryLog]

theorem tsum_dilogCos_zero (angle : ℝ) :
    ∑' j : ℕ, chapter9DilogCosTerm 0 angle j = 0 := by
  have hfun : chapter9DilogCosTerm 0 angle = fun _ => 0 := by
    funext j
    rw [dilogCos_term_eq]
    simp only [zero_pow (Nat.succ_ne_zero j), zero_mul, zero_div]
  rw [hfun]
  exact tsum_zero

theorem tsum_dilogSin_zero (angle : ℝ) :
    ∑' j : ℕ, chapter9DilogSinTerm 0 angle j = 0 := by
  have hfun : chapter9DilogSinTerm 0 angle = fun _ => 0 := by
    funext j
    rw [dilogSin_term_eq]
    simp only [zero_pow (Nat.succ_ne_zero j), zero_mul, zero_div]
  rw [hfun]
  exact tsum_zero

theorem hasSum_dilogCos_one_zero :
    HasSum (chapter9DilogCosTerm 1 0) (Real.pi ^ 2 / 6) := by
  have hcorr : ∑ i ∈ Finset.range 1, (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) i = 0 := by
    simp
  have h2 : HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2))
      (Real.pi ^ 2 / 6 +
        ∑ i ∈ Finset.range 1, (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) i) := by
    rw [hcorr, add_zero]
    exact hasSum_zeta_two
  have hbase : HasSum (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2))
      (Real.pi ^ 2 / 6) :=
    (hasSum_nat_add_iff 1).mpr h2
  have hfun : chapter9DilogCosTerm 1 0 =
      (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2)) := by
    funext j
    rw [dilogCos_term_eq]
    simp
  rw [hfun]
  exact hbase

theorem tsum_dilogSin_one_zero : ∑' j : ℕ, chapter9DilogSinTerm 1 0 j = 0 := by
  have hfun : chapter9DilogSinTerm 1 0 = fun _ => 0 := by
    funext j
    rw [dilogSin_term_eq]
    simp
  rw [hfun]
  exact tsum_zero

theorem exp_I_mul_ofReal (t : ℝ) :
    Complex.exp (Complex.I * (t : ℂ)) =
      ((Real.cos t : ℝ) : ℂ) + ((Real.sin t : ℝ) : ℂ) * Complex.I := by
  have h : (Complex.I * (t : ℂ)) = ((t : ℂ)) * Complex.I := mul_comm _ _
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem re_exp_I_mul (t : ℝ) :
    (Complex.exp (Complex.I * (t : ℂ))).re = Real.cos t := by
  rw [exp_I_mul_ofReal]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]

theorem im_exp_I_mul (t : ℝ) :
    (Complex.exp (Complex.I * (t : ℂ))).im = Real.sin t := by
  rw [exp_I_mul_ofReal]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]

theorem norm_exp_I_mul (t : ℝ) : ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (Complex.I * (t : ℂ)).re = 0 := by simp
  rw [hre, Real.exp_zero]

theorem edge_of_rho_zero {y phi : ℝ} (hy : 0 ≤ y ∧ y ≤ 1)
    (hphi : -Real.pi < phi ∧ phi ≤ Real.pi)
    (hxy : (y : ℂ) * Complex.exp (Complex.I * (phi : ℂ)) = 1) :
    y = 1 ∧ phi = 0 := by
  have hE : ‖Complex.exp (Complex.I * (phi : ℂ))‖ = 1 := norm_exp_I_mul phi
  have h1 : ‖((y : ℝ) : ℂ)‖ = 1 := by
    have h := congrArg (fun z : ℂ => ‖z‖) hxy
    rw [norm_mul, norm_one] at h
    rw [hE, mul_one] at h
    exact h
  have hy1 : y = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy.1] at h1
    exact h1
  subst hy1
  simp only [Complex.ofReal_one, one_mul] at hxy
  have hcos : Real.cos phi = 1 := by
    have h := congrArg Complex.re hxy
    rw [re_exp_I_mul, Complex.one_re] at h
    exact h
  have hphi0 : phi = 0 := by
    have hmem1 : |phi| ∈ Set.Icc 0 Real.pi :=
      Set.mem_Icc.mpr ⟨abs_nonneg _, abs_le.mpr ⟨by linarith [hphi.1], hphi.2⟩⟩
    have hmem0 : (0 : ℝ) ∈ Set.Icc 0 Real.pi :=
      Set.mem_Icc.mpr ⟨le_refl _, Real.pi_pos.le⟩
    have heq : Real.cos |phi| = Real.cos 0 := by
      rw [Real.cos_abs, hcos, Real.cos_zero]
    have hcon := Real.injOn_cos hmem1 hmem0 heq
    rwa [abs_eq_zero] at hcon
  exact ⟨rfl, hphi0⟩

theorem summable_cLi2 (z : ℂ) (hz : ‖z‖ ≤ 1) :
    Summable (fun j : ℕ => z ^ (j + 1) / ((((j + 1 : ℕ)) : ℂ) ^ 2)) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) summable_inv_succ_sq
  have hnum : ‖z‖ ^ (j + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
  have hDpos : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ) ^ 2) := by positivity
  have hD' : ‖((((j + 1 : ℕ)) : ℂ) ^ 2)‖ = ((((j + 1 : ℕ)) : ℝ) ^ 2) := by
    rw [norm_pow, Complex.norm_natCast]
  rw [norm_div, norm_pow, hD']
  exact div_le_div_of_nonneg_right hnum (le_of_lt hDpos)

theorem cpow_add (rho angle : ℝ) (j : ℕ) :
    (((rho : ℝ) : ℂ) * Complex.exp (Complex.I * (angle : ℂ))) ^ (j + 1)
      = (((rho ^ (j + 1) * Real.cos ((((j + 1 : ℕ)) : ℝ) * angle) : ℝ)) : ℂ)
        + (((rho ^ (j + 1) * Real.sin ((((j + 1 : ℕ)) : ℝ) * angle) : ℝ)) : ℂ) *
          Complex.I := by
  rw [mul_pow]
  have hE : (Complex.exp (Complex.I * (angle : ℂ))) ^ (j + 1)
      = (((Real.cos ((((j + 1 : ℕ)) : ℝ) * angle) : ℝ)) : ℂ)
        + (((Real.sin ((((j + 1 : ℕ)) : ℝ) * angle) : ℝ)) : ℂ) * Complex.I := by
    rw [← Complex.exp_nat_mul]
    have harg : ((j + 1 : ℕ) : ℂ) * (Complex.I * (angle : ℂ))
        = Complex.I * ((((((j + 1 : ℕ)) : ℝ) * angle : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [harg, exp_I_mul_ofReal]
  rw [hE]
  push_cast
  ring

theorem cLi2_cos (rho angle : ℝ) (j : ℕ) :
    (((((rho : ℝ) : ℂ) * Complex.exp (Complex.I * (angle : ℂ))) ^ (j + 1) /
      ((((j + 1 : ℕ)) : ℂ) ^ 2))).re
      = chapter9DilogCosTerm rho angle j := by
  have hD : ((((j + 1 : ℕ)) : ℂ) ^ 2) =
      ((((((j + 1 : ℕ)) : ℝ) ^ 2 : ℝ)) : ℂ) := by push_cast; ring
  rw [cpow_add, dilogCos_term_eq, hD, div_eq_mul_inv, ← Complex.ofReal_inv]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, sub_zero]
  rw [div_eq_mul_inv]

theorem cLi2_sin (rho angle : ℝ) (j : ℕ) :
    (((((rho : ℝ) : ℂ) * Complex.exp (Complex.I * (angle : ℂ))) ^ (j + 1) /
      ((((j + 1 : ℕ)) : ℂ) ^ 2))).im
      = chapter9DilogSinTerm rho angle j := by
  have hD : ((((j + 1 : ℕ)) : ℂ) ^ 2) =
      ((((((j + 1 : ℕ)) : ℝ) ^ 2 : ℝ)) : ℂ) := by push_cast; ring
  rw [cpow_add, dilogSin_term_eq, hD, div_eq_mul_inv, ← Complex.ofReal_inv]
  simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
  rw [div_eq_mul_inv]

theorem log_ofReal_mul_exp_I (r t : ℝ) (hr : 0 < r)
    (ht : -Real.pi < t ∧ t ≤ Real.pi) :
    Complex.log (((r : ℝ) : ℂ) * Complex.exp (Complex.I * (t : ℂ)))
      = (((Real.log r : ℝ)) : ℂ) + ((t : ℝ) : ℂ) * Complex.I := by
  set l : ℂ := (((Real.log r : ℝ)) : ℂ) + ((t : ℝ) : ℂ) * Complex.I with hl
  have hr0 : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  have hz : ((r : ℝ) : ℂ) * Complex.exp (Complex.I * (t : ℂ)) ≠ 0 :=
    mul_ne_zero hr0 (Complex.exp_ne_zero _)
  have hexp : Complex.exp l
      = ((r : ℝ) : ℂ) * Complex.exp (Complex.I * (t : ℂ)) := by
    rw [hl, Complex.exp_add]
    congr 1
    · rw [← Complex.ofReal_exp, Real.exp_log hr]
    · rw [mul_comm ((t : ℝ) : ℂ) Complex.I]
  have himl : l.im = t := by
    rw [hl]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
  have hlog : Complex.exp (Complex.log (((r : ℝ) : ℂ) *
      Complex.exp (Complex.I * (t : ℂ))))
      = ((r : ℝ) : ℂ) * Complex.exp (Complex.I * (t : ℂ)) :=
    Complex.exp_log hz
  have h1 : -Real.pi < (Complex.log (((r : ℝ) : ℂ) *
      Complex.exp (Complex.I * (t : ℂ)))).im := by
    rw [Complex.log_im]
    exact Complex.neg_pi_lt_arg _
  have h2 : (Complex.log (((r : ℝ) : ℂ) *
      Complex.exp (Complex.I * (t : ℂ)))).im ≤ Real.pi := by
    rw [Complex.log_im]
    exact Complex.arg_le_pi _
  have h3 : -Real.pi < l.im := by rw [himl]; exact ht.1
  have h4 : l.im ≤ Real.pi := by rw [himl]; exact ht.2
  have key_eq : Complex.exp (Complex.log (((r : ℝ) : ℂ) *
      Complex.exp (Complex.I * (t : ℂ)))) = Complex.exp l :=
    hlog.trans hexp.symm
  exact Complex.exp_inj_of_neg_pi_lt_of_le_pi h1 h2 h3 h4 key_eq

end
end Entry24Dougall
end Ramanujan.Part1Ch9
end
