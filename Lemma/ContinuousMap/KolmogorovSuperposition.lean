import Mathlib
import sympy.Basic
import sympy.Analysis.ContinuousMap.KolmogorovSuperposition

open ContinuousMap.KolmogorovSuperpositionWanted

/-- [kolmogorov_superposition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ContinuousMap/KolmogorovSuperposition.lean) -/
@[path]
private lemma kolmogorov_superposition_eq
-- given
  {n : ℕ}
  (hn : 2 ≤ n) :
-- imply
  ∃ (ψ : Fin (2 * n + 1) → Fin n → ContinuousMap (Set.Icc (0 : ℝ) 1) ℝ),
    ∀ (f : ContinuousMap (Fin n → Set.Icc (0 : ℝ) 1) ℝ),
      ∃ (φ : Fin (2 * n + 1) → ContinuousMap ℝ ℝ),
        ∀ (x : Fin n → Set.Icc (0 : ℝ) 1),
          f x = ∑ q : Fin (2 * n + 1), φ q (∑ p : Fin n, ψ q p (x p)) := by
-- proof
  apply kolmogorov_superposition hn

-- created on 2026-10-10
