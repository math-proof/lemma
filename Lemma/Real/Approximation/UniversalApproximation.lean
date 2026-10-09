import Mathlib
import sympy.Basic
import sympy.Analysis.Approximation.UniversalApproximation

/--
[universal_approximation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Approximation/UniversalApproximation.lean)
-/
@[path]
private lemma universal_approximation_eq
  {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} {σ : ℝ → ℝ}
  {f : EuclideanSpace ℝ (Fin n) → ℝ} {ε : ℝ}
-- given
  (hK : IsCompact K)
  (hσ : Continuous σ)
  (hnp : ¬ ∃ p : Polynomial ℝ, ∀ x, σ x = p.eval x)
  (hf : ContinuousOn f K)
  (hε : 0 < ε) :
-- imply
  ∃ (m : ℕ) (c : Fin m → ℝ) (W : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ),
    ∀ x ∈ K, |f x - ∑ i, c i * σ (inner ℝ (W i) x + b i)| < ε :=
-- proof
  MetaMathlibExt.universal_approximation hK hσ hnp hf hε


-- created on 2026-10-09
