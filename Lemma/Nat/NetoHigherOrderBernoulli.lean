import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NetoHigherOrderBernoulli
open Finset
open MetaMathlibExt


namespace MetaMathlibExt

/--
[higherOrderBernoulliNumber_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NetoHigherOrderBernoulli.lean)
-/
@[path]
lemma higherOrderBernoulliNumber_one
  {n : ℕ} :
-- imply
  higherOrderBernoulliNumber 1 n = (bernoulli n : ℂ) := by
-- proof
  have h1 : (1 : ℂ) = ((1 : ℕ) : ℂ) := by norm_num
  rw [h1, higherOrderBernoulliNumber_nat]
  simp only [pow_one]
  rw [bernoulliPowerSeries, PowerSeries.coeff_mk]
  rw [← map_natCast (algebraMap ℚ ℂ) n.factorial, ← map_mul]
  apply congr_arg (algebraMap ℚ ℂ)
  apply mul_div_cancel₀
  exact_mod_cast Nat.factorial_ne_zero n

end MetaMathlibExt

namespace MetaMathlibExt

/--
[neto_bernoulli_reflection](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NetoHigherOrderBernoulli.lean)
-/
@[path]
private lemma neto_bernoulli_reflection :
  PowerSeries.evalNegHom (bernoulliPowerSeries ℂ) =
    bernoulliPowerSeries ℂ * PowerSeries.exp ℂ := by
  have hB := bernoulliPowerSeries_mul_exp_sub_one ℂ
  have hfactor :
    PowerSeries.evalNegHom (PowerSeries.exp ℂ) - 1 ≠ 0 := by
    intro h
    have hc := congrArg (PowerSeries.coeff 1) (sub_eq_zero.mp h)
    norm_num [PowerSeries.evalNegHom, PowerSeries.coeff_rescale,
      PowerSeries.coeff_exp] at hc
  apply mul_right_cancel₀ hfactor
  calc
    PowerSeries.evalNegHom (bernoulliPowerSeries ℂ) *
      (PowerSeries.evalNegHom (PowerSeries.exp ℂ) - 1) =
      PowerSeries.evalNegHom
        (bernoulliPowerSeries ℂ * (PowerSeries.exp ℂ - 1)) := by
          rw [map_mul, map_sub, map_one]
    _ = -PowerSeries.X := by rw [hB, PowerSeries.evalNegHom_X]
    _ = (bernoulliPowerSeries ℂ * PowerSeries.exp ℂ) *
      (PowerSeries.evalNegHom (PowerSeries.exp ℂ) - 1) := by
      rw [mul_sub, mul_one, mul_assoc,
        PowerSeries.exp_mul_exp_neg_eq_one, mul_one]
      linear_combination hB

end MetaMathlibExt

namespace MetaMathlibExt

/--
[neto_bernoulli_power_reflection](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NetoHigherOrderBernoulli.lean)
-/
@[path]
private lemma neto_bernoulli_power_reflection (d : ℕ) :
  PowerSeries.evalNegHom (bernoulliPowerSeries ℂ ^ d) =
    bernoulliPowerSeries ℂ ^ d *
      PowerSeries.rescale (d : ℂ) (PowerSeries.exp ℂ) := by
  rw [map_pow, neto_bernoulli_reflection, mul_pow,
    PowerSeries.exp_pow_eq_rescale_exp]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[neto_iterate_derivative_evalNeg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NetoHigherOrderBernoulli.lean)
-/
@[path]
private lemma neto_iterate_derivative_evalNeg (f : PowerSeries ℂ) (l : ℕ) :
  PowerSeries.derivative^[l] (PowerSeries.evalNegHom f) =
    (-1 : ℂ) ^ l • PowerSeries.evalNegHom (PowerSeries.derivative^[l] f) := by
  ext n
  simp only [PowerSeries.coeff_iterate_derivative, PowerSeries.evalNegHom,
    PowerSeries.coeff_rescale, map_smul, smul_eq_mul]
  rw [pow_add]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[neto_derivative_rescale](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NetoHigherOrderBernoulli.lean)
-/
@[path]
private lemma neto_derivative_rescale (a : ℂ) (f : PowerSeries ℂ) :
  PowerSeries.derivative (PowerSeries.rescale a f) =
    a • PowerSeries.rescale a (PowerSeries.derivative f) := by
  ext n
  simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_rescale,
    map_smul, smul_eq_mul]
  rw [pow_succ]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[neto_iterate_derivative_rescale_exp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NetoHigherOrderBernoulli.lean)
-/
@[path]
private lemma neto_iterate_derivative_rescale_exp (a : ℂ) (r : ℕ) :
  PowerSeries.derivative^[r] (PowerSeries.rescale a (PowerSeries.exp ℂ)) =
    a ^ r • PowerSeries.rescale a (PowerSeries.exp ℂ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, Derivation.map_smul,
      neto_derivative_rescale, PowerSeries.derivative_exp, smul_smul, pow_succ]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[neto_iterate_derivative_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NetoHigherOrderBernoulli.lean)
-/
@[path]
private lemma neto_iterate_derivative_mul (p q : PowerSeries ℂ) (n : ℕ) :
  PowerSeries.derivative^[n] (p * q) =
    ∑ k ∈ range n.succ, n.choose k •
      (PowerSeries.derivative^[n - k] p * PowerSeries.derivative^[k] q) := by
  induction n with
  | zero => simp [Finset.range]
  | succ n ih =>
    calc
      PowerSeries.derivative^[n + 1] (p * q) =
        PowerSeries.derivative (∑ k ∈ range n.succ,
          n.choose k • (PowerSeries.derivative^[n - k] p *
            PowerSeries.derivative^[k] q)) := by
        rw [Function.iterate_succ_apply', ih]
      _ = (∑ k ∈ range n.succ, n.choose k •
        (PowerSeries.derivative^[n - k + 1] p *
          PowerSeries.derivative^[k] q)) +
        ∑ k ∈ range n.succ, n.choose k •
          (PowerSeries.derivative^[n - k] p *
            PowerSeries.derivative^[k + 1] q) := by
        simp only [Nat.succ_eq_add_one, map_sum, map_nsmul,
          PowerSeries.derivative.leibniz, Function.iterate_succ', Function.comp_apply]
        simp_rw [smul_add, sum_add_distrib]
        simp only [smul_eq_mul]
        rw [add_comm]
        congr 1
        apply sum_congr rfl
        intro x hx
        ring
      _ = (∑ k ∈ range n.succ, n.choose k.succ •
        (PowerSeries.derivative^[n - k] p *
          PowerSeries.derivative^[k + 1] q)) +
        1 • (PowerSeries.derivative^[n + 1] p * PowerSeries.derivative^[0] q) +
        ∑ k ∈ range n.succ, n.choose k •
          (PowerSeries.derivative^[n - k] p *
            PowerSeries.derivative^[k + 1] q) := ?_
      _ = ((∑ k ∈ range n.succ, n.choose k •
        (PowerSeries.derivative^[n - k] p *
          PowerSeries.derivative^[k + 1] q)) +
        ∑ k ∈ range n.succ, n.choose k.succ •
          (PowerSeries.derivative^[n - k] p *
            PowerSeries.derivative^[k + 1] q)) +
        1 • (PowerSeries.derivative^[n + 1] p * PowerSeries.derivative^[0] q) := by
        rw [add_comm, add_assoc]
      _ = (∑ i ∈ range n.succ, (n + 1).choose (i + 1) •
        (PowerSeries.derivative^[n + 1 - (i + 1)] p *
          PowerSeries.derivative^[i + 1] q)) +
        1 • (PowerSeries.derivative^[n + 1] p * PowerSeries.derivative^[0] q) := by
        simp_rw [Nat.choose_succ_succ, Nat.succ_sub_succ, add_smul, sum_add_distrib]
      _ = ∑ k ∈ range n.succ.succ, n.succ.choose k •
        (PowerSeries.derivative^[n.succ - k] p *
          PowerSeries.derivative^[k] q) := by
        rw [sum_range_succ' _ n.succ, Nat.choose_zero_right, tsub_zero]
    congr
    refine (sum_range_succ' _ _).trans (congr_arg₂ (fun x y => x + y) ?_ ?_)
    · rw [sum_range_succ, Nat.choose_succ_self, zero_smul, add_zero]
      refine sum_congr rfl fun k hk => ?_
      rw [mem_range] at hk
      congr
      omega
    · rw [Nat.choose_zero_right, tsub_zero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[neto_iterate_derivative_rescale_exp_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NetoHigherOrderBernoulli.lean)
-/
@[path]
private lemma neto_iterate_derivative_rescale_exp_mul
  (a : ℂ) (f : PowerSeries ℂ) (l : ℕ) :
  PowerSeries.derivative^[l]
    (PowerSeries.rescale a (PowerSeries.exp ℂ) * f) =
    PowerSeries.rescale a (PowerSeries.exp ℂ) *
      ∑ k ∈ range (l + 1),
        (a ^ (l - k) * (l.choose k : ℂ)) • PowerSeries.derivative^[k] f := by
  rw [neto_iterate_derivative_mul]
  simp_rw [neto_iterate_derivative_rescale_exp]
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  simp only [Algebra.smul_def, map_mul, map_natCast]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[neto_normalized_coeff_exp_mul_derivative](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NetoHigherOrderBernoulli.lean)
-/
@[path]
private lemma neto_normalized_coeff_exp_mul_derivative
  (a : ℂ) (f : PowerSeries ℂ) (n l : ℕ) :
  (n.factorial : ℂ) * PowerSeries.coeff n
    (PowerSeries.rescale a (PowerSeries.exp ℂ) *
      PowerSeries.derivative^[l] f) =
    ∑ k ∈ range (n + 1),
      a ^ (n - k) * (n.choose k : ℂ) *
        ((l + k).factorial : ℂ) * PowerSeries.coeff (l + k) f := by
  have hiter (k : ℕ) :
    PowerSeries.constantCoeff
      (PowerSeries.derivative^[k] (PowerSeries.derivative^[l] f)) =
      ((l + k).factorial : ℂ) * PowerSeries.coeff (l + k) f := by
    rw [← Function.iterate_add_apply PowerSeries.derivative k l f,
      PowerSeries.constantCoeff_iterate_derivative]
    rw [add_comm]
  have hE : PowerSeries.constantCoeff
    (PowerSeries.rescale a (PowerSeries.exp ℂ)) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_rescale,
      PowerSeries.coeff_exp]
    norm_num
  calc
    (n.factorial : ℂ) * PowerSeries.coeff n
      (PowerSeries.rescale a (PowerSeries.exp ℂ) *
        PowerSeries.derivative^[l] f) =
      PowerSeries.constantCoeff (PowerSeries.derivative^[n]
        (PowerSeries.rescale a (PowerSeries.exp ℂ) *
          PowerSeries.derivative^[l] f)) := by
            rw [PowerSeries.constantCoeff_iterate_derivative]
    _ = PowerSeries.constantCoeff
      (PowerSeries.rescale a (PowerSeries.exp ℂ) *
        ∑ k ∈ range (n + 1),
          (a ^ (n - k) * (n.choose k : ℂ)) •
            PowerSeries.derivative^[k] (PowerSeries.derivative^[l] f)) := by
        rw [neto_iterate_derivative_rescale_exp_mul]
    _ = ∑ k ∈ range (n + 1),
      a ^ (n - k) * (n.choose k : ℂ) *
        ((l + k).factorial : ℂ) * PowerSeries.coeff (l + k) f := by
      rw [map_mul, hE, one_mul, map_sum]
      simp_rw [PowerSeries.constantCoeff_smul, hiter]
      simp only [smul_eq_mul, mul_assoc]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[neto_evalNeg_rescale_exp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NetoHigherOrderBernoulli.lean)
-/
@[path]
private lemma neto_evalNeg_rescale_exp (a : ℂ) :
  PowerSeries.evalNegHom (PowerSeries.rescale a (PowerSeries.exp ℂ)) =
    PowerSeries.rescale (-a) (PowerSeries.exp ℂ) := by
  ext n
  simp only [PowerSeries.evalNegHom, PowerSeries.coeff_rescale]
  rw [neg_pow]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[neto_rescale_exp_evalNeg_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NetoHigherOrderBernoulli.lean)
-/
@[path]
private lemma neto_rescale_exp_evalNeg_mul (a : ℂ) :
  PowerSeries.evalNegHom (PowerSeries.rescale a (PowerSeries.exp ℂ)) *
    PowerSeries.rescale a (PowerSeries.exp ℂ) = 1 := by
  rw [neto_evalNeg_rescale_exp, mul_comm,
    PowerSeries.exp_mul_exp_eq_exp_add]
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[neto_reflected_exp_mul_derivative](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NetoHigherOrderBernoulli.lean)
-/
@[path]
private lemma neto_reflected_exp_mul_derivative
  (a : ℂ) (f : PowerSeries ℂ) (l : ℕ)
  (href : PowerSeries.evalNegHom f =
    PowerSeries.rescale a (PowerSeries.exp ℂ) * f) :
  PowerSeries.evalNegHom
    (PowerSeries.rescale a (PowerSeries.exp ℂ) *
      PowerSeries.derivative^[l] f) =
    (-1 : ℂ) ^ l •
      ∑ k ∈ range (l + 1),
        (a ^ (l - k) * (l.choose k : ℂ)) •
          PowerSeries.derivative^[k] f := by
  have hd := congrArg (fun g : PowerSeries ℂ => PowerSeries.derivative^[l] g) href
  rw [neto_iterate_derivative_evalNeg,
    neto_iterate_derivative_rescale_exp_mul] at hd
  have hrd : PowerSeries.evalNegHom (PowerSeries.derivative^[l] f) =
    (-1 : ℂ) ^ l •
      (PowerSeries.rescale a (PowerSeries.exp ℂ) *
        ∑ k ∈ range (l + 1),
          (a ^ (l - k) * (l.choose k : ℂ)) •
            PowerSeries.derivative^[k] f) := by
    have h := congrArg (fun g : PowerSeries ℂ => (-1 : ℂ) ^ l • g) hd
    simpa only [smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
      one_pow, one_smul] using h
  rw [map_mul, hrd, mul_smul_comm, ← mul_assoc,
    neto_rescale_exp_evalNeg_mul, one_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[neto_normalized_symmetry](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NetoHigherOrderBernoulli.lean)
-/
@[path]
private lemma neto_normalized_symmetry
  (a : ℂ) (f : PowerSeries ℂ) (n l : ℕ)
  (href : PowerSeries.evalNegHom f =
    PowerSeries.rescale a (PowerSeries.exp ℂ) * f) :
  (n.factorial : ℂ) * PowerSeries.coeff n
    (PowerSeries.rescale a (PowerSeries.exp ℂ) *
      PowerSeries.derivative^[l] f) =
    (-1 : ℂ) ^ (n + l) *
      ((l.factorial : ℂ) * PowerSeries.coeff l
        (PowerSeries.rescale a (PowerSeries.exp ℂ) *
          PowerSeries.derivative^[n] f)) := by
  have hc := congrArg (PowerSeries.coeff n)
    (neto_reflected_exp_mul_derivative a f l href)
  simp only [PowerSeries.evalNegHom, PowerSeries.coeff_rescale,
    PowerSeries.coeff_smul, map_sum, PowerSeries.coeff_iterate_derivative,
    smul_eq_mul] at hc
  have hcoeff :
    (-1 : ℂ) ^ n * ((n.factorial : ℂ) * PowerSeries.coeff n
      (PowerSeries.rescale a (PowerSeries.exp ℂ) *
        PowerSeries.derivative^[l] f)) =
    (-1 : ℂ) ^ l *
      ∑ k ∈ range (l + 1),
        a ^ (l - k) * (l.choose k : ℂ) *
          ((n + k).factorial : ℂ) * PowerSeries.coeff (n + k) f := by
    calc
      _ = (n.factorial : ℂ) *
        ((-1 : ℂ) ^ n * PowerSeries.coeff n
          (PowerSeries.rescale a (PowerSeries.exp ℂ) *
            PowerSeries.derivative^[l] f)) := by ring
      _ = (n.factorial : ℂ) *
        ((-1 : ℂ) ^ l *
          ∑ k ∈ range (l + 1),
            a ^ (l - k) * (l.choose k : ℂ) *
              (((n + 1).ascFactorial k : ℂ) *
                PowerSeries.coeff (n + k) f)) := by rw [hc]
      _ = (-1 : ℂ) ^ l * ((n.factorial : ℂ) *
        ∑ k ∈ range (l + 1),
          a ^ (l - k) * (l.choose k : ℂ) *
            (((n + 1).ascFactorial k : ℂ) *
              PowerSeries.coeff (n + k) f)) := by ring
      _ = (-1 : ℂ) ^ l *
        ∑ k ∈ range (l + 1), (n.factorial : ℂ) *
          (a ^ (l - k) * (l.choose k : ℂ) *
            (((n + 1).ascFactorial k : ℂ) *
              PowerSeries.coeff (n + k) f)) := by rw [mul_sum]
      _ = _ := by
        apply congr_arg ((-1 : ℂ) ^ l * ·)
        apply sum_congr rfl
        intro k hk
        have hfac : (n.factorial : ℂ) * ((n + 1).ascFactorial k : ℂ) =
          ((n + k).factorial : ℂ) := by
          norm_cast
          exact Nat.factorial_mul_ascFactorial n k
        calc
          _ = a ^ (l - k) * (l.choose k : ℂ) *
            (((n.factorial : ℂ) * ((n + 1).ascFactorial k : ℂ)) *
              PowerSeries.coeff (n + k) f) := by ring
          _ = _ := by
            rw [hfac]
            simp only [mul_assoc]
  have hsum := hcoeff
  rw [neto_normalized_coeff_exp_mul_derivative] at hsum
  rw [neto_normalized_coeff_exp_mul_derivative,
    neto_normalized_coeff_exp_mul_derivative]
  calc
    _ = (-1 : ℂ) ^ n *
      ((-1 : ℂ) ^ n *
        ∑ k ∈ range (n + 1),
          a ^ (n - k) * (n.choose k : ℂ) *
            ((l + k).factorial : ℂ) * PowerSeries.coeff (l + k) f) := by
      rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      norm_num
    _ = (-1 : ℂ) ^ n *
      ((-1 : ℂ) ^ l *
        ∑ k ∈ range (l + 1),
          a ^ (l - k) * (l.choose k : ℂ) *
            ((n + k).factorial : ℂ) * PowerSeries.coeff (n + k) f) := by
      rw [hsum]
    _ = _ := by rw [pow_add, mul_assoc]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[neto_identity_nat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NetoHigherOrderBernoulli.lean)
-/
@[path]
private lemma neto_identity_nat (d n l : ℕ) :
  (∑ k ∈ range (n + 1),
    (d : ℂ) ^ (n - k) * (n.choose k : ℂ) *
      higherOrderBernoulliNumber (d : ℂ) (l + k)) =
  (-1 : ℂ) ^ (n + l) *
    ∑ k ∈ range (l + 1),
      (d : ℂ) ^ (l - k) * (l.choose k : ℂ) *
        higherOrderBernoulliNumber (d : ℂ) (n + k) := by
  simp_rw [higherOrderBernoulliNumber_nat]
  have href : PowerSeries.evalNegHom (bernoulliPowerSeries ℂ ^ d) =
    PowerSeries.rescale (d : ℂ) (PowerSeries.exp ℂ) *
      bernoulliPowerSeries ℂ ^ d := by
    rw [neto_bernoulli_power_reflection, mul_comm]
  have hs := neto_normalized_symmetry (d : ℂ)
    (bernoulliPowerSeries ℂ ^ d) n l href
  rw [neto_normalized_coeff_exp_mul_derivative,
    neto_normalized_coeff_exp_mul_derivative] at hs
  simpa only [mul_assoc] using hs

end MetaMathlibExt

/--
[higherOrderBernoulliNumber_nat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NetoHigherOrderBernoulli.lean)
-/
@[path]
private lemma higherOrderBernoulliNumber_nat_eq
  {d n : ℕ} :
-- imply
  higherOrderBernoulliNumber (d : ℂ) n =
    (n.factorial : ℂ) * PowerSeries.coeff n (bernoulliPowerSeries ℂ ^ d) := by
-- proof
  apply MetaMathlibExt.higherOrderBernoulliNumber_nat d n

/--
[neto_higher_order_bernoulli_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NetoHigherOrderBernoulli.lean)
-/
@[path]
private lemma neto_higher_order_bernoulli_identity_eq
  {x : ℂ}
  {n ℓ : ℕ} :
-- imply
  (∑ k ∈ Finset.range (n + 1),
    x ^ (n - k) * (Nat.choose n k : ℂ) * higherOrderBernoulliNumber x (ℓ + k)) =
    (-1 : ℂ) ^ (n + ℓ) *
    ∑ k ∈ Finset.range (ℓ + 1),
    x ^ (ℓ - k) * (Nat.choose ℓ k : ℂ) * higherOrderBernoulliNumber x (n + k) := by
-- proof
  apply MetaMathlibExt.neto_higher_order_bernoulli_identity x n ℓ


-- created on 2026-10-20
-- updated on 2026-10-23
