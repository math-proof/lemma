import Mathlib
import sympy.Basic
import Def.NumberTheory.LSeries.PrimeLog
open scoped LSeries.notation
open Nat.Primes


namespace Nat.Primes

/--
[summable_log_mul_rpow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/PrimeLog.lean)
-/
@[path]
private lemma summable_log_mul_rpow {σ₀ : ℝ} (hσ : 1 / 2 < σ₀) :
  Summable
    (fun p : Nat.Primes => Real.log ((p : ℕ) : ℝ) *
      ((((p : ℕ)) : ℝ) ^ (-(2 * σ₀)))) := by
  have hε : (0 : ℝ) < (2 * σ₀ - 1) / 2 := by linarith
  set ε : ℝ := (2 * σ₀ - 1) / 2 with hεdef
  have hsum : Summable
    (fun p : Nat.Primes => (1 / ε : ℝ) * ((((p : ℕ)) : ℝ) ^ (-(1 + ε)))) :=
    Summable.mul_left (1 / ε)
      ((Nat.Primes.summable_rpow (r := -(1 + ε))).mpr (by linarith))
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hsum
  · have h1 : (1 : ℝ) ≤ (((p : ℕ)) : ℝ) := by
    have h2 : (2 : ℝ) ≤ (((p : ℕ)) : ℝ) := by
      exact_mod_cast Nat.Prime.two_le p.prop
    linarith
    exact mul_nonneg (Real.log_nonneg h1)
      (Real.rpow_nonneg (by linarith) _)
  · have h2 : (2 : ℝ) ≤ (((p : ℕ)) : ℝ) := by
    exact_mod_cast Nat.Prime.two_le p.prop
    have hpos : (0 : ℝ) < (((p : ℕ)) : ℝ) := by linarith
    have hplog : Real.log (((p : ℕ)) : ℝ) ≤ ((((p : ℕ)) : ℝ) ^ ε / ε) :=
      Real.log_le_rpow_div (by linarith) hε
    calc Real.log _ * _ ^ (-(2 * σ₀))
      ≤ (((((p : ℕ)) : ℝ) ^ ε / ε)) * ((((p : ℕ)) : ℝ) ^ (-(2 * σ₀))) :=
        mul_le_mul_of_nonneg_right hplog (Real.rpow_nonneg (le_of_lt hpos) _)
      _ = (1 / ε) * (((((p : ℕ)) : ℝ) ^ ε) * ((((p : ℕ)) : ℝ) ^ (-(2 * σ₀)))) := by
        ring
      _ = (1 / ε) * ((((p : ℕ)) : ℝ) ^ (-(1 + ε))) := by
        have hex : ε + -(2 * σ₀) = -(1 + ε) := by
          rw [hεdef]
          ring
        rw [← Real.rpow_add hpos, hex]

end Nat.Primes

namespace Nat.Primes

/--
[summable_correctionMajorant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/PrimeLog.lean)
-/
@[path]
private lemma summable_correctionMajorant {σ₀ : ℝ} (hσ : 1 / 2 < σ₀) :
  Summable
    (fun x : Nat.Primes × ℕ => Real.log (((x.1 : ℕ)) : ℝ) *
      ((((x.1 : ℕ)) : ℝ) ^ (-(((x.2 + 2 : ℕ)) : ℝ) * σ₀))) := by
  have hσpos : (0 : ℝ) < σ₀ := by linarith
  set q : ℝ := (2 : ℝ) ^ (-σ₀) with hqdef
  have hqnn : 0 ≤ q := by
    rw [hqdef]
    exact Real.rpow_nonneg (by norm_num) _
  have h2σ : (1 : ℝ) < (2 : ℝ) ^ σ₀ := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hσpos
    rwa [Real.rpow_zero] at h
  have hq1 : q < 1 := by
    rw [hqdef, Real.rpow_neg (by norm_num)]
    exact inv_lt_one_of_one_lt₀ h2σ
  have hw : Summable (fun k : ℕ => q ^ k) := summable_geometric_of_lt_one hqnn hq1
  have hv : Summable
    (fun p : Nat.Primes => Real.log (((p : ℕ)) : ℝ) *
      ((((p : ℕ)) : ℝ) ^ (-(2 * σ₀)))) :=
    summable_log_mul_rpow hσ
  have hprod := hv.mul_of_nonneg hw
    (fun p => mul_nonneg (Real.log_nonneg (by
      have h2 : (2 : ℝ) ≤ (((p : ℕ)) : ℝ) := by
        exact_mod_cast Nat.Prime.two_le p.prop
      linarith)) (Real.rpow_nonneg (by
      have h2 : (2 : ℝ) ≤ (((p : ℕ)) : ℝ) := by
        exact_mod_cast Nat.Prime.two_le p.prop
      linarith) _))
    (fun k => pow_nonneg hqnn _)
  refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) hprod
  · obtain ⟨p, k⟩ := x
    have h2 : (2 : ℝ) ≤ (((p : ℕ)) : ℝ) := by
      exact_mod_cast Nat.Prime.two_le p.prop
    exact mul_nonneg (Real.log_nonneg (by linarith)) (Real.rpow_nonneg (by linarith) _)
  · obtain ⟨p, k⟩ := x
    have hp2 : (2 : ℝ) ≤ (((p : ℕ)) : ℝ) := by
      exact_mod_cast Nat.Prime.two_le p.prop
    have hppos : (0 : ℝ) < (((p : ℕ)) : ℝ) := by linarith
    have hplog : 0 ≤ Real.log (((p : ℕ)) : ℝ) := Real.log_nonneg (by linarith)
    have hexp : (-((((k + 2 : ℕ))) : ℝ)) * σ₀ = -(2 * σ₀) + (k : ℝ) * (-σ₀) := by
      push_cast
      ring
    have hbase : ((((p : ℕ)) : ℝ) ^ (-σ₀)) ≤ q := by
      have h1 : ((((p : ℕ)) : ℝ) ^ (-σ₀)) = ((((p : ℕ)) : ℝ) ^ σ₀)⁻¹ :=
        Real.rpow_neg (le_of_lt hppos) _
      have h2 : q = (((2 : ℝ) ^ σ₀))⁻¹ := by
        rw [hqdef, Real.rpow_neg (by norm_num)]
      rw [h1, h2]
      exact (inv_le_inv₀ (Real.rpow_pos_of_pos hppos _)
        (Real.rpow_pos_of_pos (by norm_num) _)).mpr
        (Real.rpow_le_rpow (by norm_num) hp2 (le_of_lt hσpos))
    have hnpow : ((((p : ℕ)) : ℝ) ^ ((k : ℝ) * (-σ₀))) =
      (((((p : ℕ)) : ℝ) ^ (-σ₀)) ^ k) := by
      have hex : (k : ℝ) * (-σ₀) = (-σ₀) * (k : ℝ) := by ring
      rw [hex, Real.rpow_mul (le_of_lt hppos), Real.rpow_natCast]
    change Real.log _ * _ ^ _ ≤ (Real.log _ * _ ^ _) * q ^ k
    calc Real.log (((p : ℕ)) : ℝ) * ((((p : ℕ)) : ℝ) ^ (-(((k + 2 : ℕ)) : ℝ) * σ₀))
      = ((Real.log (((p : ℕ)) : ℝ)) * ((((p : ℕ)) : ℝ) ^ (-(2 * σ₀)))) *
        ((((p : ℕ)) : ℝ) ^ ((k : ℝ) * (-σ₀))) := by
        rw [hexp, Real.rpow_add hppos]
        ring
      _ ≤ ((Real.log (((p : ℕ)) : ℝ)) * ((((p : ℕ)) : ℝ) ^ (-(2 * σ₀)))) * q ^ k := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hplog
          (Real.rpow_nonneg (le_of_lt hppos) _))
        rw [hnpow]
        exact pow_le_pow_left₀ (Real.rpow_nonneg (le_of_lt hppos) _) hbase k

end Nat.Primes

namespace Nat.Primes

/--
[norm_correctionTerm_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/PrimeLog.lean)
-/
@[path]
private lemma norm_correctionTerm_le (p : Nat.Primes) (k : ℕ) (w : ℂ) (σ₀ : ℝ)
  (hw : σ₀ ≤ w.re) :
  ‖logDirichletCorrectionTerm p k w‖
    ≤ Real.log (((p : ℕ)) : ℝ) *
      ((((p : ℕ)) : ℝ) ^ (-((((k + 2 : ℕ))) : ℝ) * σ₀)) := by
  have h2 : (2 : ℝ) ≤ (((p : ℕ)) : ℝ) := by
    exact_mod_cast Nat.Prime.two_le p.prop
  have hlognn : 0 ≤ Real.log (((p : ℕ)) : ℝ) := Real.log_nonneg (by linarith)
  have hN1 : (1 : ℕ) ≤ (p : ℕ) ^ (k + 2) :=
    Nat.one_le_pow _ _ (Nat.Prime.pos p.prop)
  have hNpos : (0 : ℝ) < (((p : ℕ) ^ (k + 2) : ℕ) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hN1
  have h1le : (1 : ℝ) ≤ (((p : ℕ) ^ (k + 2) : ℕ) : ℝ) := by
    exact_mod_cast hN1
  have hbase : (Nat.cast ((p : ℕ) ^ (k + 2)) : ℂ)
    = ((((p : ℕ) ^ (k + 2) : ℕ) : ℝ) : ℂ) :=
    (Complex.ofReal_natCast _).symm
  have hNσ : ((((p : ℕ) ^ (k + 2) : ℕ) : ℝ)) ^ σ₀
    = ((((p : ℕ)) : ℝ) ^ (((((k + 2 : ℕ))) : ℝ) * σ₀)) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  have hle : ((((p : ℕ) ^ (k + 2) : ℕ) : ℝ)) ^ σ₀
    ≤ ((((p : ℕ) ^ (k + 2) : ℕ) : ℝ)) ^ (w.re) :=
    Real.rpow_le_rpow_of_exponent_le h1le hw
  change ‖(Real.log (((p : ℕ)) : ℝ) : ℂ) /
    (Nat.cast ((p : ℕ) ^ (k + 2)) : ℂ) ^ w‖ ≤ _
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlognn, hbase,
    Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
  calc Real.log (((p : ℕ)) : ℝ) / ((((p : ℕ) ^ (k + 2) : ℕ) : ℝ)) ^ (w.re)
    ≤ Real.log (((p : ℕ)) : ℝ) / ((((p : ℕ) ^ (k + 2) : ℕ) : ℝ)) ^ σ₀ :=
      div_le_div_of_nonneg_left hlognn (Real.rpow_pos_of_pos hNpos _) hle
    _ = Real.log (((p : ℕ)) : ℝ) *
      ((((p : ℕ)) : ℝ) ^ (-((((k + 2 : ℕ))) : ℝ) * σ₀)) := by
      rw [hNσ, div_eq_mul_inv, ← Real.rpow_neg (by linarith), neg_mul]

end Nat.Primes

namespace Nat.Primes

/--
[differentiable_correctionTerm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/PrimeLog.lean)
-/
@[path]
private lemma differentiable_correctionTerm (p : Nat.Primes) (k : ℕ) :
  Differentiable ℂ (fun w => logDirichletCorrectionTerm p k w) := by
  have hN0 : (Nat.cast ((p : ℕ) ^ (k + 2)) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero _ (ne_of_gt (Nat.Prime.pos p.prop))
  change Differentiable ℂ
    (fun w => (Real.log (((p : ℕ)) : ℝ) : ℂ) / (Nat.cast ((p : ℕ) ^ (k + 2)) : ℂ) ^ w)
  refine Differentiable.div (differentiable_const _) ?_ ?_
  · exact differentiable_id.const_cpow (Or.inl hN0)
  · intro w
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hN0)

end Nat.Primes

namespace Nat.Primes

/--
[summable_logDirichletCorrectionTerm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/PrimeLog.lean)
-/
@[path]
private lemma summable_logDirichletCorrectionTerm {s : ℂ} (hs : 1 / 2 < s.re) :
  Summable (fun x : Nat.Primes × ℕ => logDirichletCorrectionTerm x.1 x.2 s) := by
  have hsum := summable_correctionMajorant (σ₀ := s.re) hs
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => ?_) hsum
  obtain ⟨p, k⟩ := x
  exact norm_correctionTerm_le p k s s.re le_rfl

end Nat.Primes

namespace Nat.Primes

/--
[logDirichletCorrection_analyticOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/PrimeLog.lean)
-/
@[path]
lemma logDirichletCorrection_analyticOn
  :
-- imply
  AnalyticOnNhd ℂ logDirichletCorrection {s | 1 / 2 < s.re} := by
-- proof
  intro s₀ hs₀
  have hs₀' : (1 / 2 : ℝ) < s₀.re := hs₀
  set σ₀ : ℝ := (1 / 2 + s₀.re) / 2 with hσ₀def
  have hσ : (1 / 2 : ℝ) < σ₀ := by linarith
  have hσs : σ₀ < s₀.re := by linarith
  have hUopen : IsOpen {w : ℂ | σ₀ < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ logDirichletCorrection {w : ℂ | σ₀ < w.re} := by
    have hbase := Complex.differentiableOn_tsum_of_summable_norm
      (F := fun x : Nat.Primes × ℕ => logDirichletCorrectionTerm x.1 x.2)
      (U := {w : ℂ | σ₀ < w.re}) (summable_correctionMajorant hσ)
      (fun x => (differentiable_correctionTerm x.1 x.2).differentiableOn)
      hUopen
      (fun x w hw => norm_correctionTerm_le x.1 x.2 w σ₀
        (le_of_lt (show σ₀ < w.re from hw)))
    exact hbase
  have hanal := hdiff.analyticOnNhd hUopen
  exact hanal s₀ hσs

end Nat.Primes

namespace Nat.Primes

/--
[logDirichlet_vonMangoldt_split](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/PrimeLog.lean)
-/
@[path]
lemma logDirichlet_vonMangoldt_split
  {s : ℂ}
-- given
  (hs : 1 < s.re) :
-- imply
  LSeries ↗ArithmeticFunction.vonMangoldt s
    = logDirichletSeries s + logDirichletCorrection s := by
-- proof
  have hsum := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hsup : Function.support (LSeries.term ↗ArithmeticFunction.vonMangoldt s)
    ⊆ {n | IsPrimePow n} := by
    intro n hn
    rw [Function.mem_support] at hn
    change IsPrimePow n
    by_contra hcon
    apply hn
    by_cases h0 : n = 0
    · simp [LSeries.term, h0]
    · have hΛ : ((((ArithmeticFunction.vonMangoldt n : ℝ))) : ℂ) = 0 := by
      have h0' : ArithmeticFunction.vonMangoldt n = 0 :=
        ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hcon
      rw [h0']
      rfl
      rw [LSeries.term_of_ne_zero h0, hΛ, zero_div]
  have hsplit := tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers
    (f := LSeries.term ↗ArithmeticFunction.vonMangoldt s) hsum hsup
  have hcorr := summable_logDirichletCorrectionTerm (s := s) (by linarith : (1 / 2 : ℝ) < s.re)
  have hterm : ∀ p : Nat.Primes, LSeries.term ↗ArithmeticFunction.vonMangoldt s ↑p
    = (Real.log ((((p : ℕ))) : ℝ) : ℂ) / (((p : ℕ)) : ℂ) ^ s := by
    intro p
    rw [LSeries.term_of_ne_zero p.prop.ne_zero]
    congr 1
    show ((((ArithmeticFunction.vonMangoldt ↑p : ℝ))) : ℂ) = _
    rw [ArithmeticFunction.vonMangoldt_apply_prime p.prop]
  have hterm2 : ∀ p : Nat.Primes, ∀ k : ℕ,
    LSeries.term ↗ArithmeticFunction.vonMangoldt s (↑p ^ (k + 2))
      = logDirichletCorrectionTerm p k s := by
    intro p k
    have hN : (↑p : ℕ) ^ (k + 2) ≠ 0 := pow_ne_zero _ p.prop.ne_zero
    rw [LSeries.term_of_ne_zero hN]
    change (↗ArithmeticFunction.vonMangoldt) _ / _ = logDirichletCorrectionTerm p k s
    unfold logDirichletCorrectionTerm
    congr 1
    change ((((ArithmeticFunction.vonMangoldt (↑p ^ (k + 2)) : ℝ))) : ℂ) = _
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega : k + 2 ≠ 0),
      ArithmeticFunction.vonMangoldt_apply_prime p.prop]
  change ∑' n, LSeries.term ↗ArithmeticFunction.vonMangoldt s n = _ + _
  rw [hsplit]
  congr 1
  · exact tsum_congr fun p => hterm p
  · change ∑' (p : Nat.Primes) (k : ℕ),
    LSeries.term ↗ArithmeticFunction.vonMangoldt s (↑p ^ (k + 2))
    = ∑' x : Nat.Primes × ℕ, logDirichletCorrectionTerm x.1 x.2 s
    rw [Summable.tsum_prod hcorr]
    exact tsum_congr fun p => tsum_congr fun k => hterm2 p k

end Nat.Primes

namespace Nat.Primes

/--
[logDirichletSeries_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/PrimeLog.lean)
-/
@[path]
lemma logDirichletSeries_eq
  {s : ℂ}
-- given
  (hs : 1 < s.re) :
-- imply
  logDirichletSeries s
    = -deriv riemannZeta s / riemannZeta s - logDirichletCorrection s := by
-- proof
  have hΛ := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have hsplit := logDirichlet_vonMangoldt_split hs
  have hcomb : logDirichletSeries s + logDirichletCorrection s
    = -deriv riemannZeta s / riemannZeta s := by
    rwa [← hsplit]
  linear_combination hcomb

end Nat.Primes

namespace Nat.Primes

/--
[logDirichletContinuation_meromorphic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/PrimeLog.lean)
-/
@[path]
lemma logDirichletContinuation_meromorphic
  :
-- imply
  MeromorphicOn logDirichletContinuation {s | 1 / 2 < s.re} := by
-- proof
  have hanal : AnalyticOnNhd ℂ riemannZeta₁ {s : ℂ | 1 / 2 < s.re} :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)
  have hmero := hanal.meromorphicOn
  have hC := logDirichletCorrection_analyticOn.meromorphicOn
  change MeromorphicOn
    (fun s => -(deriv riemannZeta₁ s / riemannZeta₁ s) - logDirichletCorrection s) _
  exact (hmero.deriv.div hmero).neg.sub hC

end Nat.Primes

namespace Nat.Primes

/--
[logDirichletContinuation_analyticOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/PrimeLog.lean)
-/
@[path]
lemma logDirichletContinuation_analyticOn
  :
-- imply
  AnalyticOnNhd ℂ logDirichletContinuation {s | 1 ≤ s.re} := by
-- proof
  have huniv : AnalyticOnNhd ℂ riemannZeta₁ Set.univ :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd isOpen_univ
  have hsub : {s : ℂ | 1 ≤ s.re} ⊆ {s : ℂ | 1 / 2 < s.re} := by
    intro x hx
    change (1 / 2 : ℝ) < x.re
    have hx' : (1 : ℝ) ≤ x.re := hx
    linarith
  have hζ := huniv.mono (s := {s : ℂ | 1 ≤ s.re}) (Set.subset_univ _)
  have hζd := huniv.deriv.mono (s := {s : ℂ | 1 ≤ s.re}) (Set.subset_univ _)
  have hC := logDirichletCorrection_analyticOn.mono hsub
  have hdiv := hζd.div hζ
    (fun x hx => riemannZeta₁_ne_zero_of_one_le_re (show (1 : ℝ) ≤ x.re from hx))
  change AnalyticOnNhd ℂ
    (fun s => -(deriv riemannZeta₁ s / riemannZeta₁ s) - logDirichletCorrection s) _
  exact hdiv.neg.sub hC

end Nat.Primes

namespace Nat.Primes

/--
[logDirichletContinuation_agree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/PrimeLog.lean)
-/
@[path]
lemma logDirichletContinuation_agree
  :
-- imply
  Set.EqOn logDirichletContinuation
    (fun s => logDirichletSeries s - 1 / (s - 1)) {s | 1 < s.re} := by
-- proof
  intro s hs
  have hs' : (1 : ℝ) < s.re := hs
  change -(deriv riemannZeta₁ s / riemannZeta₁ s) - logDirichletCorrection s
    = logDirichletSeries s - 1 / (s - 1)
  have hPhi := logDirichletSeries_eq hs'
  have hne1 : s ≠ 1 := by
    intro h
    rw [h] at hs'
    simp at hs'
  have hζ1 : riemannZeta₁ s ≠ 0 :=
    riemannZeta₁_ne_zero_of_one_le_re (le_of_lt hs')
  have hsub1 : s - 1 ≠ 0 := sub_ne_zero.mpr hne1
  have hinv : (s - 1)⁻¹ ≠ 0 := inv_ne_zero hsub1
  have hid : -deriv riemannZeta s / riemannZeta s
    = 1 / (s - 1) - deriv riemannZeta₁ s / riemannZeta₁ s := by
    rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hne1, riemannZeta_eq_inv_sub_mul hne1]
    field_simp
    ring
  rw [hPhi, hid]
  ring

end Nat.Primes

namespace Nat.Primes

/--
[logDirichlet_meromorphicContinuation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/PrimeLog.lean)
-/
@[path]
lemma logDirichlet_meromorphicContinuation
  :
-- imply
  ∃ g : ℂ → ℂ,
    MeromorphicOn g {s | 1 / 2 < s.re} ∧
    AnalyticOnNhd ℂ g {s | 1 ≤ s.re} ∧
    Set.EqOn g (fun s => logDirichletSeries s - 1 / (s - 1))
    {s | 1 < s.re} :=
-- proof
  ⟨logDirichletContinuation, logDirichletContinuation_meromorphic,
    logDirichletContinuation_analyticOn, logDirichletContinuation_agree⟩

end Nat.Primes

/--
[riemannZeta₁_ne_zero_of_one_le_re](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/PrimeLog.lean)
-/
@[path]
lemma riemannZeta₁_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
  riemannZeta₁ s ≠ 0 := by
  obtain rfl | hne := eq_or_ne s 1
  · rw [riemannZeta₁_one]
    exact one_ne_zero
  · have hζ := riemannZeta_ne_zero_of_one_le_re hs
    rw [riemannZeta_eq_inv_sub_mul hne] at hζ
    exact (mul_ne_zero_iff.mp hζ).2



-- created on 2026-10-20
-- updated on 2026-10-23
