import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Bernoulli.BernoulliSecondKindAsymptotic
open MetaMathlibExt


/--
[bernoulli_second_kind_asymptotic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/BernoulliSecondKindAsymptotic.lean)
-/
@[path]
private lemma bernoulli_second_kind_asymptotic_eq
  {b β : ℕ → ℝ}
-- given
  (hb : ∀ n : ℕ, b n = (∫ x in (0 : ℝ)..1, ∏ j ∈ Finset.range n, (x - (j : ℝ))) / (Nat.factorial n : ℝ))
  (hβ : ∀ k : ℕ, β k = (-1 : ℝ) ^ k * iteratedDeriv (k + 1) (fun s : ℝ => (Real.Gamma s)⁻¹) (0 : ℝ)) :
-- imply
  ∀ m : ℕ, Asymptotics.IsLittleO Filter.atTop
    (fun n : ℕ => b n -
    (((-1 : ℝ) ^ (n + 1) / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) * ∑ k ∈ Finset.range (m + 1), β k /
    (Real.log (n : ℝ)) ^ k)) (fun n : ℕ => 1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ (m + 2))) := by
-- proof
  apply MetaMathlibExt.bernoulli_second_kind_asymptotic b β hb hβ


-- created on 2026-10-20
