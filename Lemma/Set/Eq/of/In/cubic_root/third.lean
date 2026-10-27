import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Notation.Analysis.Complex.Complexes
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {p : ℂ}
-- given
  (h₀ : -Real.pi < Complex.arg p)
  (h₁ : Complex.arg p ≤ -Real.pi / 3) :
-- imply
  (p * ((-1 / 2 : ℂ) + Complex.I * (Real.sqrt 3 / 2))) ^ 3 = p ^ 3 ∧
    -Real.pi < Complex.arg p ∧ Complex.arg p ≤ -Real.pi / 3 := by
-- proof
  have hsq : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have h3 : (Real.sqrt 3 : ℂ) ^ 3 = 3 * Real.sqrt 3 := by
    rw [pow_succ, hsq]
  have hω : ((-1 / 2 : ℂ) + Complex.I * (Real.sqrt 3 / 2)) ^ 3 = 1 := by
    ring_nf
    simp [h3, hsq, Complex.I_sq]
    ring
  refine ⟨?_, h₀, h₁⟩
  calc
    _ = p ^ 3 * ((-1 / 2 : ℂ) + Complex.I * (Real.sqrt 3 / 2)) ^ 3 := by ring
    _ = p ^ 3 * 1 := by rw [hω]
    _ = p ^ 3 := by ring


-- created on 2021-03-08
-- updated on 2026-10-26
