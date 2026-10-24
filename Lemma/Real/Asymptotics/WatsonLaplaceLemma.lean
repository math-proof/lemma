import Mathlib
import sympy.Basic
import sympy.series.asymptotics.WatsonLaplaceLemma

open MetaMathlibExt


namespace MetaMathlibExt

/--
[watson_aux_integrable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Asymptotics/WatsonLaplaceLemma.lean)
-/
@[path]
private lemma watson_aux_integrable (m : ℝ) (hm : 0 < m) (n : ℕ) :
  MeasureTheory.IntegrableOn (fun s : ℝ => s ^ n * Real.exp (-m * s)) (Set.Ioi 0) := by
  have hs : (-1 : ℝ) < (n : ℝ) := by
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := m)
    hs one_pos hm
  simp only [Real.rpow_one] at h
  apply h.congr
  filter_upwards with s
  rw [Real.rpow_natCast]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[watson_aux_value](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Asymptotics/WatsonLaplaceLemma.lean)
-/
@[path]
private lemma watson_aux_value (m : ℝ) (hm : 0 < m) (n : ℕ) :
  (∫ s in Set.Ioi 0, s ^ n * Real.exp (-m * s)) = (n.factorial : ℝ) / m ^ (n + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (r := m)
    (by positivity) hm
  rw [Real.Gamma_nat_eq_factorial] at h
  have e1 : ((n : ℝ) + 1 - 1) = (n : ℝ) := by ring
  have e3 : ((n : ℝ) + 1) = (((n + 1 : ℕ)) : ℝ) := by push_cast; ring
  have hfun : (fun t : ℝ => t ^ ((n : ℝ) + 1 - 1) * Real.exp (-(m * t)))
    = (fun s : ℝ => s ^ n * Real.exp (-m * s)) := by
    funext s
    rw [e1, Real.rpow_natCast]
    have he : (-(m * s)) = (-m * s) := by ring
    rw [he]
  rw [hfun] at h
  have hRHS : (1 / m) ^ ((n : ℝ) + 1) * ((n.factorial : ℕ) : ℝ)
    = ((n.factorial : ℕ) : ℝ) / m ^ (n + 1) := by
    rw [e3, Real.rpow_natCast, div_pow, one_pow]
    ring
  rwa [hRHS] at h

end MetaMathlibExt

/--
[watson_laplace_integral_asymptotic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Asymptotics/WatsonLaplaceLemma.lean)
-/
@[path]
lemma watson_laplace_integral_asymptotic
-- given
  (g : ℝ → ℝ)
  (hconv : ∃ m₀ : ℝ, ∀ m ≥ m₀, MeasureTheory.IntegrableOn
    (fun s : ℝ => g s * Real.exp (-m * s)) (Set.Ioi 0))
  (c : ℕ → ℝ)
  (hlocal : ∀ N : ℕ, Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0))
    (fun s : ℝ => g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1)))
    (fun s : ℝ => s ^ (N + 1))) :
-- imply
  ∀ N : ℕ, Asymptotics.IsBigO Filter.atTop
    (fun m : ℝ => (∫ s in Set.Ioi 0, g s * Real.exp (-m * s)) -
      (∑ k ∈ Finset.range N,
        ((Nat.factorial (k + 1) : ℕ) : ℝ) * c (k + 1) / m ^ (k + 2)))
    (fun m : ℝ => 1 / m ^ (N + 2)) :=
-- proof
  MetaMathlibExt.watson_laplace_integral_asymptotic g c hlocal hconv


-- created on 2026-10-09
-- updated on 2026-10-23
