/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Ramanujan/Part1Ch3Section8Example1Asymptotic.lean -/


import Def.NumberTheory.Ramanujan.Part1Ch3Section8Example1Asymptotic
import Lemma.Nat.Ramanujan.Part1Ch3Section8Example1Asymptotic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum


namespace MathlibExtTest.NumberTheory.Ramanujan.Part1Ch3Section8Example1Asymptotic

open MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Section8Example1Asymptotic

-- The one-term factorial series gives the first-order expansion of `1 / (z + 1)`.
example :
    ∃ C R : ℝ, 0 < R ∧ 0 ≤ C ∧ ∀ x : ℝ, R ≤ x →
      ‖1 / ((x : ℂ) + 1) - 1 / (x : ℂ)‖ ≤ C / ‖(x : ℂ)‖ ^ 2 := by
  have heps : 0 < Real.pi / 4 := by positivity
  have hepslt : Real.pi / 4 < Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hsum : ∀ z : ℂ, (∀ n : ℕ, z ≠ -((n + 1 : ℕ) : ℂ)) →
      (⊥ : WithBot ℝ) < (↑z.re : WithBot ℝ) →
      HasSum (fun j : ℕ => (-1 : ℂ) ^ j * (if j = 0 then 1 else 0) /
        ∏ k ∈ Finset.range (j + 1), (z + ((k + 1 : ℕ) : ℂ))) (1 / (z + 1)) := by
    intro z hpole hlam
    refine (hasSum_ite_eq 0 (1 / (z + 1))).congr_fun ?_
    intro j
    by_cases hj : j = 0
    · subst j
      simp
    · simp [hj]
  obtain ⟨C, R, hR, hC, hbound⟩ :=
    ramanujan_part1_ch3_section8_example1_asymptotic
      (a := fun j => if j = 0 then 1 else 0) (ψ := fun z => 1 / (z + 1))
      (lam := (⊥ : WithBot ℝ)) (eps := Real.pi / 4) heps (by simp) (by simpa using hepslt)
      hsum 0
  refine ⟨C, max R 1, by positivity, hC, ?_⟩
  intro x hx
  have hRx : R ≤ x := (le_max_left R 1).trans hx
  have hxone : 1 ≤ x := (le_max_right R 1).trans hx
  have hx0 : 0 ≤ x := zero_le_one.trans hxone
  have hpole : ∀ n : ℕ, (x : ℂ) ≠ -((n + 1 : ℕ) : ℂ) := by
    intro n hn
    have hre := congrArg Complex.re hn
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hsector :
      (((⊥ : WithBot ℝ) = ⊥ → |Complex.arg (x : ℂ)| ≤ Real.pi / 2 - Real.pi / 4) ∧
        ∀ r : ℝ, (⊥ : WithBot ℝ) = (↑r : WithBot ℝ) →
          |Complex.arg ((x : ℂ) - (r : ℂ))| ≤ Real.pi / 2 - Real.pi / 4) := by
    constructor
    · intro h
      rw [Complex.arg_ofReal_of_nonneg hx0, abs_zero]
      linarith
    · intro r hr
      simp at hr
  have hnorm : R ≤ ‖(x : ℂ)‖ := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0] using hRx
  have hb := hbound (x : ℂ) hpole (by simp) hsector hnorm
  simpa [Finset.sum_range_succ, Nat.stirlingSecond_self] using hb

end MathlibExtTest.NumberTheory.Ramanujan.Part1Ch3Section8Example1Asymptotic
