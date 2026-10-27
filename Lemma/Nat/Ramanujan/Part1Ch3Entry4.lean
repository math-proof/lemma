import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.Ramanujan.Part1Ch3Entry4
open Entry9IiGeneralizedbellgeneratingDefining (generalizedBellGenerating)
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry4


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[hasSum_exp_series](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma hasSum_exp_series (z : ℂ) :
  HasSum (fun n => z ^ n / (Nat.factorial n : ℂ)) (Complex.exp z) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) z
  rwa [Complex.exp_eq_exp_ℂ]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[tail_exp_series](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma tail_exp_series (w : ℂ) :
  w * (∑' n : ℕ, w ^ n / ((Nat.factorial (n + 1) : ℕ) : ℂ)) =
    Complex.exp w - 1 := by
  have hsum := hasSum_exp_series w
  have hsumm := hsum.summable
  have hval := hsum.tsum_eq
  have hsplit := hsumm.tsum_eq_zero_add
  have key : w * (∑' n : ℕ, w ^ n / ((Nat.factorial (n + 1) : ℕ) : ℂ)) =
    ∑' b : ℕ, w ^ (b + 1) / ((Nat.factorial (b + 1) : ℕ) : ℂ) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [pow_succ']
    ring
  rw [← hval, hsplit, key]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  ring

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[norm_inner_term](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma norm_inner_term (x : ℂ) (n j : ℕ) :
  ‖(((j + 1 : ℂ)) ^ n * x ^ (j + 1) / (Nat.factorial j : ℂ))‖
    = ((j : ℝ) + 1) ^ n * ‖x‖ ^ (j + 1) / (Nat.factorial j : ℝ) := by
  rw [norm_div, norm_mul, norm_pow, norm_pow]
  congr 1
  · congr 1
    rw [← Nat.cast_add_one, Complex.norm_natCast, Nat.cast_add, Nat.cast_one]
  · rw [Complex.norm_natCast]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[fact_le_succ_fact](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma fact_le_succ_fact (n : ℕ) :
  (Nat.factorial n : ℝ) ≤ ((Nat.factorial (n + 1) : ℕ) : ℝ) := by
  rw [Nat.factorial_succ]
  push_cast
  apply le_mul_of_one_le_left (by positivity)
  have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[summable_pow_div_succ_factorial_real](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma summable_pow_div_succ_factorial_real (W : ℝ) (hW : 0 ≤ W) :
  Summable (fun n => W ^ n / ((Nat.factorial (n + 1) : ℕ) : ℝ)) := by
  apply Summable.of_nonneg_of_le (g := fun n => W ^ n / ((Nat.factorial (n + 1) : ℕ) : ℝ))
    (f := fun n => W ^ n / (Nat.factorial n : ℝ))
  · intro n
    positivity
  · intro n
    have h1 : (0 : ℝ) < (Nat.factorial n : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos n)
    have hfle := fact_le_succ_fact n
    gcongr
  · exact Real.summable_pow_div_factorial W

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[summable_pow_div_succ_factorial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma summable_pow_div_succ_factorial (w : ℂ) :
  Summable (fun n => w ^ n / ((Nat.factorial (n + 1) : ℕ) : ℂ)) := by
  apply Summable.of_norm
  have hnorm : ∀ n : ℕ, ‖w ^ n / ((Nat.factorial (n + 1) : ℕ) : ℂ)‖
    = ‖w‖ ^ n / ((Nat.factorial (n + 1) : ℕ) : ℝ) := by
    intro n
    rw [norm_div, norm_pow, Complex.norm_natCast]
  simp only [hnorm]
  apply Summable.of_nonneg_of_le
    (g := fun n => ‖w‖ ^ n / ((Nat.factorial (n + 1) : ℕ) : ℝ))
    (f := fun n => ‖w‖ ^ n / (Nat.factorial n : ℝ))
  · intro n
    positivity
  · intro n
    have h1 : (0 : ℝ) < (Nat.factorial n : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos n)
    have hfle := fact_le_succ_fact n
    gcongr
  · exact Real.summable_pow_div_factorial ‖w‖

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[real_exp_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma real_exp_tsum (W : ℝ) :
  (∑' n : ℕ, W ^ n / (Nat.factorial n : ℝ)) = Real.exp W := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) W
  rwa [Real.exp_eq_exp_ℝ]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[fiber_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma fiber_summable (a x : ℂ) (j : ℕ) : Summable (fun n => T a x j n) := by
  have heq : (fun n => T a x j n)
    = (fun n => (a * (Complex.exp (-x) * (x ^ (j + 1) / (Nat.factorial j : ℂ))))
      * ((a * (j + 1 : ℂ)) ^ n / ((Nat.factorial (n + 1) : ℕ) : ℂ))) := by
    funext n
    unfold T
    rw [mul_pow]
    ring
  rw [heq]
  exact (summable_pow_div_succ_factorial _).mul_left _

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[norm_T](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma norm_T (a x : ℂ) (j n : ℕ) :
  ‖T a x j n‖ = ‖a‖ ^ (n + 1) / ((Nat.factorial (n + 1) : ℕ) : ℝ) *
    (‖Complex.exp (-x)‖ * (((j : ℝ) + 1) ^ n * ‖x‖ ^ (j + 1) / (Nat.factorial j : ℝ))) := by
  have h1 : ‖((j + 1 : ℂ))‖ = (j : ℝ) + 1 := by
    rw [← Nat.cast_add_one, Complex.norm_natCast, Nat.cast_add, Nat.cast_one]
  unfold T
  simp only [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
  rw [h1]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[fiber_norm_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma fiber_norm_summable (a x : ℂ) (j : ℕ) : Summable (fun n => ‖T a x j n‖) := by
  have heq : (fun n => ‖T a x j n‖)
    = (fun n => (‖a‖ * (‖Complex.exp (-x)‖ * (‖x‖ ^ (j + 1) / (Nat.factorial j : ℝ))))
      * ((‖a‖ * ((j : ℝ) + 1)) ^ n / ((Nat.factorial (n + 1) : ℕ) : ℝ))) := by
    funext n
    rw [norm_T, mul_pow]
    ring
  rw [heq]
  exact (summable_pow_div_succ_factorial_real _ (by positivity)).mul_left _

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[fiber_norm_tsum_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma fiber_norm_tsum_le (a x : ℂ) (j : ℕ) :
  (∑' n, ‖T a x j n‖)
    ≤ (‖a‖ * (‖Complex.exp (-x)‖ * (‖x‖ ^ (j + 1) / (Nat.factorial j : ℝ)))) *
      Real.exp (‖a‖ * ((j : ℝ) + 1)) := by
  have heq : (fun n => ‖T a x j n‖)
    = (fun n => (‖a‖ * (‖Complex.exp (-x)‖ * (‖x‖ ^ (j + 1) / (Nat.factorial j : ℝ))))
      * ((‖a‖ * ((j : ℝ) + 1)) ^ n / ((Nat.factorial (n + 1) : ℕ) : ℝ))) := by
    funext n
    rw [norm_T, mul_pow]
    ring
  have hCnn : 0 ≤ ‖a‖ * (‖Complex.exp (-x)‖ * (‖x‖ ^ (j + 1) / (Nat.factorial j : ℝ))) := by
    positivity
  have hsum1 := fiber_norm_summable a x j
  rw [heq] at hsum1
  have hsum2 := summable_pow_div_succ_factorial_real _ (show (0:ℝ) ≤ ‖a‖ * ((j:ℝ)+1) by positivity)
  have hsum3 := Real.summable_pow_div_factorial (‖a‖ * ((j : ℝ) + 1))
  rw [heq, tsum_mul_left]
  apply mul_le_mul_of_nonneg_left _ hCnn
  calc (∑' n, (‖a‖ * (↑j + 1)) ^ n / ((Nat.factorial (n + 1) : ℕ) : ℝ))
    ≤ ∑' n, (‖a‖ * (↑j + 1)) ^ n / (Nat.factorial n : ℝ) := by
      apply Summable.tsum_le_tsum _ hsum2 hsum3
      intro n
      have hfle := fact_le_succ_fact n
      have hpos : (0:ℝ) ≤ (‖a‖ * (↑j + 1)) ^ n := by positivity
      gcongr
    _ = Real.exp (‖a‖ * (↑j + 1)) := real_exp_tsum _

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[outer_majorant_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma outer_majorant_summable (a x : ℂ) :
  Summable (fun j => (‖a‖ * (‖Complex.exp (-x)‖ * (‖x‖ ^ (j + 1) / (Nat.factorial j : ℝ)))) *
    Real.exp (‖a‖ * ((j : ℝ) + 1))) := by
  have heq : (fun j => (‖a‖ * (‖Complex.exp (-x)‖ * (‖x‖ ^ (j + 1) / (Nat.factorial j : ℝ)))) *
    Real.exp (‖a‖ * ((j : ℝ) + 1)))
    = (fun j => (‖a‖ * (‖Complex.exp (-x)‖ * (‖x‖ * Real.exp ‖a‖))) *
      ((‖x‖ * Real.exp ‖a‖) ^ j / (Nat.factorial j : ℝ))) := by
    funext j
    have h1 : ‖a‖ * ((j : ℝ) + 1) = (j : ℝ) * ‖a‖ + ‖a‖ := by ring
    rw [mul_pow, h1, Real.exp_add, Real.exp_nat_mul]
    ring
  rw [heq]
  exact (Real.summable_pow_div_factorial _).mul_left _

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[summable_norm_T](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma summable_norm_T (a x : ℂ) :
  Summable (fun p : ℕ × ℕ => ‖T a x p.1 p.2‖) := by
  have h := summable_prod_of_nonneg (f := fun p : ℕ × ℕ => ‖T a x p.1 p.2‖)
    (fun _ => norm_nonneg _)
  apply h.mpr
  refine ⟨fun j => fiber_norm_summable a x j, ?_⟩
  apply Summable.of_nonneg_of_le (g := fun j => ∑' n, ‖T a x j n‖)
    (f := fun j => (‖a‖ * (‖Complex.exp (-x)‖ * (‖x‖ ^ (j + 1) / (Nat.factorial j : ℝ)))) *
      Real.exp (‖a‖ * ((j : ℝ) + 1)))
  · intro j
    exact tsum_nonneg (fun n => norm_nonneg _)
  · intro j
    exact fiber_norm_tsum_le a x j
  · exact outer_majorant_summable a x

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[summable_T](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma summable_T (a x : ℂ) : Summable (fun p : ℕ × ℕ => T a x p.1 p.2) :=
  Summable.of_norm (summable_norm_T a x)

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[tail_exp_series'](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma tail_exp_series' (w : ℂ) :
  (∑' n, w ^ (n + 1) / ((Nat.factorial (n + 1) : ℕ) : ℂ)) = Complex.exp w - 1 := by
  have h := tail_exp_series w
  have heq : (fun n => w ^ (n + 1) / ((Nat.factorial (n + 1) : ℕ) : ℂ))
    = (fun n => w * (w ^ n / ((Nat.factorial (n + 1) : ℕ) : ℂ))) := by
    funext n
    rw [pow_succ']
    ring
  rwa [heq, tsum_mul_left]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[coe_add_one_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma coe_add_one_ne_zero (j : ℕ) : ((j : ℂ) + 1) ≠ 0 := by
  have h : ((j : ℂ) + 1) = ((j + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [h]
  exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[fiber_value](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma fiber_value (a x : ℂ) (ha : a ≠ 0) (j : ℕ) :
  (∑' n, T a x j n) = Complex.exp (-x) *
    (x ^ (j + 1) * (Complex.exp (a * ((j : ℂ) + 1)) - 1) /
      ((Nat.factorial (j + 1) : ℕ) : ℂ)) := by
  have hw : a * ((j : ℂ) + 1) ≠ 0 := mul_ne_zero ha (coe_add_one_ne_zero j)
  have heq : (fun n => T a x j n)
    = (fun n => (a * (Complex.exp (-x) * (x ^ (j + 1) / (Nat.factorial j : ℂ))))
      * ((a * ((j : ℂ) + 1)) ^ n / ((Nat.factorial (n + 1) : ℕ) : ℂ))) := by
    funext n
    unfold T
    rw [mul_pow]
    ring
  have htail := tail_exp_series (a * ((j : ℂ) + 1))
  have hS : (∑' n, (a * ((j : ℂ) + 1)) ^ n / ((Nat.factorial (n + 1) : ℕ) : ℂ))
    = (Complex.exp (a * ((j : ℂ) + 1)) - 1) / (a * ((j : ℂ) + 1)) := by
    rwa [eq_div_iff hw, mul_comm]
  have hfact : ((Nat.factorial (j + 1) : ℕ) : ℂ)
    = ((j : ℂ) + 1) * (Nat.factorial j : ℂ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hfj : (Nat.factorial j : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  rw [heq, tsum_mul_left, hS, hfact]
  field_simp

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[htail_summ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma htail_summ (w : ℂ) :
  Summable (fun j => w ^ (j + 1) / ((Nat.factorial (j + 1) : ℕ) : ℂ)) := by
  have h := (hasSum_exp_series w).summable.comp_injective Nat.succ_injective
  simpa [Function.comp_def, Nat.succ_eq_add_one] using h

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[hexp_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma hexp_pow (a : ℂ) (j : ℕ) :
  Complex.exp (a * ((j : ℂ) + 1)) = (Complex.exp a) ^ (j + 1) := by
  have h1 : a * ((j : ℂ) + 1) = ((j + 1 : ℕ) : ℂ) * a := by push_cast; ring
  rw [h1, Complex.exp_nat_mul]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[outer_value](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma outer_value (a x : ℂ) :
  (∑' (j : ℕ), Complex.exp (-x) *
    (x ^ (j + 1) * (Complex.exp (a * ((j : ℂ) + 1)) - 1) / ((Nat.factorial (j + 1) : ℕ) : ℂ)))
  = Complex.exp (x * (Complex.exp a - 1)) - 1 := by
  have heq : (fun (j : ℕ) => Complex.exp (-x) *
    (x ^ (j + 1) * (Complex.exp (a * ((j : ℂ) + 1)) - 1) / ((Nat.factorial (j + 1) : ℕ) : ℂ)))
    = (fun (j : ℕ) => Complex.exp (-x) *
      (((x * Complex.exp a) ^ (j + 1) - x ^ (j + 1)) / ((Nat.factorial (j + 1) : ℕ) : ℂ))) := by
    funext j
    rw [hexp_pow a j, mul_pow]
    ring
  have hs1 := htail_summ (x * Complex.exp a)
  have hs2 := htail_summ x
  have hsub : (∑' j, ((x * Complex.exp a) ^ (j + 1) - x ^ (j + 1)) /
    ((Nat.factorial (j + 1) : ℕ) : ℂ))
    = (Complex.exp (x * Complex.exp a) - 1) - (Complex.exp x - 1) := by
    have hsplit : (fun (j : ℕ) => ((x * Complex.exp a) ^ (j + 1) - x ^ (j + 1)) /
      ((Nat.factorial (j + 1) : ℕ) : ℂ))
      = (fun (j : ℕ) => (x * Complex.exp a) ^ (j + 1) / ((Nat.factorial (j + 1) : ℕ) : ℂ) -
        x ^ (j + 1) / ((Nat.factorial (j + 1) : ℕ) : ℂ)) := by
      funext j
      ring
    rw [hsplit, hs1.tsum_sub hs2, tail_exp_series', tail_exp_series']
  have e1 : Complex.exp (-x) * Complex.exp (x * Complex.exp a)
    = Complex.exp (x * (Complex.exp a - 1)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have e2 : Complex.exp (-x) * Complex.exp x = 1 := by
    rw [← Complex.exp_add]
    simp
  rw [heq, tsum_mul_left, hsub]
  have hdist : Complex.exp (-x) * ((Complex.exp (x * Complex.exp a) - 1) - (Complex.exp x - 1))
    = (Complex.exp (-x) * Complex.exp (x * Complex.exp a)) -
      (Complex.exp (-x) * Complex.exp x) := by
    ring
  rw [hdist, e1, e2]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[inner_norm_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma inner_norm_summable (x : ℂ) (n : ℕ) :
  Summable (fun j : ℕ => ((j : ℝ) + 1) ^ n * ‖x‖ ^ (j + 1) / (Nat.factorial j : ℝ)) := by
  simpa only [norm_inner_term] using
    Entry4InnerSummable.ramanujan_part1_ch3_entry4_inner_summable x n

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[inner_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma inner_summable (x : ℂ) (n : ℕ) :
  Summable (fun j : ℕ => (((j + 1 : ℂ)) ^ n * x ^ (j + 1) / (Nat.factorial j : ℂ))) :=
  (Entry4InnerSummable.ramanujan_part1_ch3_entry4_inner_summable x n).of_norm

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[generalizedBellGenerating_zero_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma generalizedBellGenerating_zero_one (x : ℂ) (n : ℕ) :
  generalizedBellGenerating 0 1 x n =
    Complex.exp (-x) * ∑' (j : ℕ), ((j + 1 : ℂ) ^ n * x ^ (j + 1) / (Nat.factorial j : ℂ)) := by
  simp [generalizedBellGenerating]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[fiber_summable_j](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma fiber_summable_j (a x : ℂ) (n : ℕ) : Summable (fun (j : ℕ) => T a x j n) := by
  have heq : (fun (j : ℕ) => T a x j n)
    = (fun (j : ℕ) => (a ^ (n + 1) / ((Nat.factorial (n + 1) : ℕ) : ℂ) * Complex.exp (-x)) *
      (((j + 1 : ℂ)) ^ n * x ^ (j + 1) / (Nat.factorial j : ℂ))) := by
    funext j
    unfold T
    ring
  rw [heq]
  exact (inner_summable x n).mul_left _

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[fiberN_norm_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma fiberN_norm_summable (a x : ℂ) (n : ℕ) : Summable (fun (j : ℕ) => ‖T a x j n‖) := by
  have heq : (fun (j : ℕ) => ‖T a x j n‖)
    = (fun (j : ℕ) => (‖a‖ ^ (n + 1) / ((Nat.factorial (n + 1) : ℕ) : ℝ) * ‖Complex.exp (-x)‖) *
      (((j : ℝ) + 1) ^ n * ‖x‖ ^ (j + 1) / (Nat.factorial j : ℝ))) := by
    funext j
    rw [norm_T]
    ring
  rw [heq]
  exact (inner_norm_summable x n).mul_left _

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[U_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma U_succ (a x : ℂ) (n : ℕ) : U a x (n + 1) = ∑' j, T a x j n := by
  have h1 : n + 1 ≠ 0 := Nat.succ_ne_zero n
  unfold U
  simp only [h1, ite_false, Nat.add_sub_cancel]
  rw [generalizedBellGenerating_zero_one]
  unfold T
  rw [tsum_mul_left, tsum_mul_left]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[U_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma U_zero (a x : ℂ) : U a x 0 = 1 := by
  simp [U]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[hTswap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma hTswap (a x : ℂ) : Summable (fun p : ℕ × ℕ => T a x p.2 p.1) := by
  have h := summable_T a x
  have heq : (fun p : ℕ × ℕ => T a x p.2 p.1)
    = (fun p : ℕ × ℕ => T a x p.1 p.2) ∘ ⇑(Equiv.prodComm ℕ ℕ) := by
    funext p
    rfl
  rw [heq]
  exact ((Equiv.prodComm ℕ ℕ).summable_iff).mpr h

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[hTnorm_swap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma hTnorm_swap (a x : ℂ) : Summable (fun p : ℕ × ℕ => ‖T a x p.2 p.1‖) := by
  have h := summable_norm_T a x
  have heq : (fun p : ℕ × ℕ => ‖T a x p.2 p.1‖)
    = (fun p : ℕ × ℕ => ‖T a x p.1 p.2‖) ∘ ⇑(Equiv.prodComm ℕ ℕ) := by
    funext p
    rfl
  rw [heq]
  exact ((Equiv.prodComm ℕ ℕ).summable_iff).mpr h

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[hUtail_hasSum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma hUtail_hasSum (a x : ℂ) :
  HasSum (fun n => ∑' j, T a x j n) (∑' p : ℕ × ℕ, T a x p.2 p.1) :=
  HasSum.prod_fiberwise (hTswap a x).hasSum (fun n => (fiber_summable_j a x n).hasSum)

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[hG_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma hG_summable (a x : ℂ) : Summable (fun n => ∑' j, ‖T a x j n‖) :=
  (HasSum.prod_fiberwise (hTnorm_swap a x).hasSum
    (fun n => (fiberN_norm_summable a x n).hasSum)).summable

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[hsumU_of](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma hsumU_of (a x : ℂ) : Summable (U a x) := by
  have hUshift : Summable (fun n => U a x (n + 1)) := by
    simpa [U_succ] using (hUtail_hasSum a x).summable
  exact ((summable_nat_add_iff (f := U a x) 1).mp hUshift)

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[hnormU_of](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma hnormU_of (a x : ℂ) : Summable (fun n => ‖U a x n‖) := by
  have hshift : Summable (fun n => ‖U a x (n + 1)‖) := by
    apply Summable.of_nonneg_of_le (g := fun n => ‖U a x (n + 1)‖)
      (f := fun n => ∑' j, ‖T a x j n‖)
    · intro n
      exact norm_nonneg _
    · intro n
      rw [U_succ]
      exact norm_tsum_le_tsum_norm (fiberN_norm_summable a x n)
    · exact hG_summable a x
  exact ((summable_nat_add_iff (f := fun n => ‖U a x n‖) 1).mp hshift)

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[hval_of](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma hval_of (a x : ℂ) (ha : a ≠ 0) :
  (∑' n, U a x n) = Complex.exp (x * (Complex.exp a - 1)) := by
  have hsumU := hsumU_of a x
  rw [hsumU.tsum_eq_zero_add, U_zero]
  have htail_eq : (∑' n, U a x (n + 1)) = ∑' n, ∑' j, T a x j n := by
    apply tsum_congr
    intro n
    exact U_succ a x n
  have hswap_sum : (∑' n, ∑' j, T a x j n) = ∑' p : ℕ × ℕ, T a x p.2 p.1 :=
    ((hTswap a x).tsum_prod).symm
  have hprod_sum : (∑' p : ℕ × ℕ, T a x p.2 p.1) = ∑' p : ℕ × ℕ, T a x p.1 p.2 :=
    Equiv.tsum_eq (Equiv.prodComm ℕ ℕ) (fun p : ℕ × ℕ => T a x p.1 p.2)
  have hprod_sum2 : (∑' p : ℕ × ℕ, T a x p.1 p.2) = ∑' j, ∑' n, T a x j n :=
    (summable_T a x).tsum_prod
  have hfib : (∑' j, ∑' n, T a x j n)
    = ∑' (j : ℕ), Complex.exp (-x) *
      (x ^ (j + 1) * (Complex.exp (a * ((j : ℂ) + 1)) - 1) /
        ((Nat.factorial (j + 1) : ℕ) : ℂ)) := by
    apply tsum_congr
    intro j
    exact fiber_value a x ha j
  rw [htail_eq, hswap_sum, hprod_sum, hprod_sum2, hfib, outer_value]
  ring

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[main_entry4](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma main_entry4 (a x : ℂ) :
  HasSum (U a x) (Complex.exp (x * (Complex.exp a - 1))) ∧ Summable (fun n => ‖U a x n‖) := by
  by_cases ha : a = 0
  · subst ha
    have hUs : ∀ n, U 0 x (n + 1) = 0 := by
      intro n
      simp only [U, zero_pow (Nat.succ_ne_zero n), zero_div, zero_mul]
    have hshad : Summable (fun n => U 0 x (n + 1)) := by
      have heq : (fun n => U 0 x (n + 1)) = (fun _ => (0 : ℂ)) := funext hUs
      rwa [heq]
    have hsumU : Summable (U 0 x) := ((summable_nat_add_iff (f := U 0 x) 1).mp hshad)
    have hval : (∑' n, U 0 x n) = Complex.exp (x * (Complex.exp 0 - 1)) := by
      rw [hsumU.tsum_eq_zero_add, U_zero]
      have htail : (∑' n, U 0 x (n + 1)) = 0 := by
        have heq : (fun n => U 0 x (n + 1)) = (fun _ => (0 : ℂ)) := funext hUs
        rw [heq, tsum_zero]
      rw [htail, add_zero, Complex.exp_zero, sub_self, mul_zero, Complex.exp_zero]
    refine ⟨?_, ?_⟩
    · rw [← hval]
      exact hsumU.hasSum
    · have hshadN : Summable (fun n => ‖U 0 x (n + 1)‖) := by
      have heq : (fun n => ‖U 0 x (n + 1)‖) = (fun _ => (0 : ℝ)) := by
        funext n
        rw [hUs n, norm_zero]
      rwa [heq]
      exact ((summable_nat_add_iff (f := fun n => ‖U 0 x n‖) 1).mp hshadN)
  · refine ⟨?_, hnormU_of a x⟩
    have hsumU := hsumU_of a x
    have hval := hval_of a x ha
    rwa [← hval]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4

/--
[ramanujan_part1_ch3_entry4](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
lemma ramanujan_part1_ch3_entry4
  {a x : ℂ} :
-- imply
  HasSum (fun n : ℕ => a ^ n / (Nat.factorial n : ℂ) *
    (if n = 0 then (1 : ℂ) else generalizedBellGenerating 0 1 x (n - 1)))
    (Complex.exp (x * (Complex.exp a - 1))) ∧
    Summable (fun n : ℕ => ‖a ^ n / (Nat.factorial n : ℂ) *
    (if n = 0 then (1 : ℂ) else generalizedBellGenerating 0 1 x (n - 1))‖) := by
-- proof
  exact main_entry4 a x

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4


-- created on 2026-10-20
-- updated on 2026-10-26
