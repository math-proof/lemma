/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Asymptotics/CatalanAsymptoticExpansion.lean -/


import Def.Analysis.Asymptotics.CatalanAsymptoticExpansion
import Lemma.Real.Asymptotics.CatalanAsymptoticExpansion


namespace MathlibExtTest.Analysis.Asymptotics.CatalanAsymptoticExpansion

open MetaMathlibExt

open Filter

open scoped BigOperators

-- Checks the public lemma on a nontrivial logarithmic step at second order.
example (c : ℝ) (hc : 0 < c) :
    Tendsto
      (fun n : ℕ =>
        (n + c : ℝ) ^ 2 *
          (Real.log (1 + 1 / (n + c : ℝ)) - 1 / (n + c : ℝ) +
            1 / (2 * (n + c : ℝ) ^ 2)))
      atTop (nhds 0) := by
  have hx : Tendsto (fun n : ℕ => (n + c : ℝ)) atTop atTop := by
    exact Filter.tendsto_atTop_add_const_right atTop c tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => 1 / (n + c : ℝ)) atTop (nhds 0) :=
    hx.const_div_atTop 1
  have harg : Tendsto (fun n : ℕ => 1 + 1 / (n + c : ℝ)) atTop (nhds 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add hinv
  have hu : Tendsto (fun n : ℕ => Real.log (1 + 1 / (n + c : ℝ)))
      atTop (nhds 0) := by
    change Tendsto (Real.log ∘ fun n : ℕ => 1 + 1 / (n + c : ℝ)) atTop (nhds 0)
    simpa only [Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp harg
  have hstep : ∀ᶠ n : ℕ in atTop,
      Real.log (1 + 1 / (((n + 1 : ℕ) : ℝ) + c)) -
          Real.log (1 + 1 / (n + c : ℝ)) =
        Real.log (1 + 2 / (n + c : ℝ)) - Real.log (1 + 0 / (n + c : ℝ)) +
          (0 - 2) * Real.log (1 + 1 / (n + c : ℝ)) := by
    filter_upwards with n
    rw [show (((n + 1 : ℕ) : ℝ) + c) = (n + c : ℝ) + 1 by push_cast; ring]
    let x : ℝ := n + c
    have hx0 : x ≠ 0 := by
      dsimp [x]
      positivity
    have hx1 : x + 1 ≠ 0 := by positivity
    have hx2 : x + 2 ≠ 0 := by positivity
    rw [show 1 + 1 / (x + 1) = (x + 2) / (x + 1) by
        field_simp
        ring,
      show 1 + 1 / x = (x + 1) / x by field_simp,
      show 1 + 2 / x = (x + 2) / x by field_simp,
      Real.log_div hx2 hx1, Real.log_div hx1 hx0, Real.log_div hx2 hx0]
    norm_num
    ring
  have h := Real.tendsto_pow_mul_sub_bernoulli_sum_of_log_diff
    (u := fun n : ℕ => Real.log (1 + 1 / (n + c : ℝ))) 2 0 c hu hstep 2
  refine h.congr' ?_
  filter_upwards with n
  norm_num [Finset.sum_range_succ, Polynomial.bernoulli_def, bernoulli_zero,
    bernoulli_one, bernoulli_two, bernoulli_eq_zero_of_odd]
  ring_nf
  simp

-- Checks the frozen theorem's first expansion coefficient at `m = 1`.
example (E : ℕ → ℤ)
    (hE : E 0 = 1 ∧ ∀ n : ℕ, 0 < n →
      (∑ j ∈ Finset.range (n / 2 + 1),
        (n.choose (2 * j) : ℤ) * E (n - 2 * j)) = 0) :
    Tendsto
      (fun n : ℕ =>
        n * (Real.log ((catalan n : ℝ) *
          (n * Real.sqrt (Real.pi * n)) / 4 ^ n) + 9 / (8 * n)))
      atTop (nhds 0) := by
  have h := (MetaMathlibExt.catalan_stirling_asymptotic_expansions E hE).1 1
  refine h.congr' ?_
  filter_upwards with n
  norm_num [Finset.sum_range_succ, bernoulli_two]
  ring_nf
  simp

-- Checks that the first shifted logarithmic coefficient vanishes at `c = 3/4`.
example :
    Tendsto
      (fun n : ℕ =>
        (n + 3 / 4 : ℝ) *
          Real.log ((catalan n : ℝ) *
            Real.sqrt (Real.pi * (n + 3 / 4 : ℝ) ^ 3) / 4 ^ n))
      atTop (nhds 0) := by
  have h := tendsto_pow_mul_log_catalan_sub_bernoulli_sum (3 / 4) 1
  refine h.congr' ?_
  filter_upwards with n
  norm_num [Finset.sum_range_succ, Polynomial.bernoulli_def, bernoulli_zero,
    bernoulli_one, bernoulli_two, Polynomial.aeval_def]

end MathlibExtTest.Analysis.Asymptotics.CatalanAsymptoticExpansion
