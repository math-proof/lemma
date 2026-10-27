import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MetaMathlibExt

/--
[exp_hasSum_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTransformExponentialGeneratingFunction.lean)
-/
@[path]
its exponential generating function multiplied by `exp`.
Source: Ayhan Dil, Veli Kurt, and Mehmet Cenkci, *Algorithms for Bernoulli
and Related Polynomials*, Journal of Integer Sequences 10 (2007), Article
07.5.4, <https://cs.uwaterloo.ca/journals/JIS/VOL10/Dil/dil11.tex>,
Proposition `prop2` (proof attributed to Seidel), lines 221-233; the
binomial-transform relation `a_0^n = Σᵢ C(n,i) a_i^0` is equation (8)/(9),
lines 188-199.
`b` is the binomial transform of `a`, `A` its exponential generating
function, and the conclusion is the EGF of `b`. The formulation is pointwise:
it assumes convergence of the EGF of `a` only at the argument `t` under
consideration. -/
private lemma exp_hasSum_aux (t : ℝ) :
  HasSum (fun m : ℕ => t ^ m / (m.factorial : ℝ)) (Real.exp t) := by
  have h := NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) (𝔸 := ℝ) t
  simp only [NormedSpace.expSeries_apply_eq_div] at h
  rwa [← Real.exp_eq_exp_ℝ] at h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[exponentialGeneratingFunction_binomialTransform](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTransformExponentialGeneratingFunction.lean)
-/
@[path]
lemma exponentialGeneratingFunction_binomialTransform
  {a b : ℕ → ℝ}
  {A : ℝ → ℝ}
-- given
  (hbinomial : ∀ n : ℕ, b n = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a k) :
-- imply
  ∀ t : ℝ, HasSum (fun n : ℕ => a n * t ^ n / n.factorial) (A t) →
    HasSum (fun n : ℕ => b n * t ^ n / n.factorial)
    (Real.exp t * A t) := by
-- proof
  intro t hA
  have he : HasSum (fun m : ℕ => t ^ m / (m.factorial : ℝ)) (Real.exp t) :=
    exp_hasSum_aux t
  -- In finite dimensions, unconditional convergence implies absolute convergence.
  have hfN : Summable fun n : ℕ => ‖a n * t ^ n / (n.factorial : ℝ)‖ :=
    hA.summable.norm
  have heN : Summable fun m : ℕ => ‖t ^ m / (m.factorial : ℝ)‖ :=
    he.summable.norm
  -- Cauchy product of the two EGF series.
  have hprod := hasSum_sum_range_mul_of_summable_norm hfN heN
  rw [hA.tsum_eq, he.tsum_eq] at hprod
  -- Each Cauchy-product term equals the corresponding `b` EGF term.
  have hterm : ∀ n : ℕ,
    (∑ k ∈ Finset.range (n + 1),
      (a k * t ^ k / (k.factorial : ℝ)) * (t ^ (n - k) / ((n - k).factorial : ℝ)))
      = b n * t ^ n / (n.factorial : ℝ) := by
    intro n
    rw [hbinomial n, Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hfact : (n.choose k : ℝ) * (k.factorial : ℝ) * ((n - k).factorial : ℝ)
      = (n.factorial : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
    have hpow : t ^ k * t ^ (n - k) = t ^ n := by
      rw [← pow_add, Nat.add_sub_cancel' hkn]
    have hkne : (k.factorial : ℝ) * ((n - k).factorial : ℝ) ≠ 0 := by
      apply mul_ne_zero
      · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hne : (n.factorial : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [div_mul_div_comm,
      show a k * t ^ k * t ^ (n - k) = a k * (t ^ k * t ^ (n - k)) from by ring,
      hpow]
    rw [div_eq_div_iff hkne hne]
    linear_combination -(a k * t ^ n) * hfact
  have h2 := hprod.congr_fun (fun n => (hterm n).symm)
  rwa [mul_comm (A t) (Real.exp t)] at h2
end



-- created on 2026-10-20
-- updated on 2026-10-26
