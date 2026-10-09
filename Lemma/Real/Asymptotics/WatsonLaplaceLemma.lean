import Mathlib
import sympy.Basic
import sympy.Analysis.Asymptotics.WatsonLaplaceLemma

open MetaMathlibExt

/--
[watson_laplace_integral_asymptotic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Asymptotics/WatsonLaplaceLemma.lean)
-/
@[path]
private lemma watson_laplace_integral_asymptotic_eq
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
