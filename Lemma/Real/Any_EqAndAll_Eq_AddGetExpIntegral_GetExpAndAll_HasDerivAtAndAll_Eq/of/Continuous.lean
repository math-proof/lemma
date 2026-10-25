import Mathlib
import sympy.Basic
import Theorem.Analysis.ODE.Duhamel

/--
[Duhamel](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/Duhamel.lean)
-/
@[path]
private lemma duhamel_variation_of_constants_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (b : ℝ → E)
  (hb : Continuous b)
  (A : E →L[ℝ] E) (t₀ : ℝ) (x₀ : E) :
-- imply
  ∃ x : ℝ → E, x t₀ = x₀ ∧
    (∀ t, x t = (NormedSpace.exp ((t - t₀) • A)) x₀ +
      ∫ s in t₀..t, (NormedSpace.exp ((t - s) • A)) (b s)) ∧
    (∀ t, HasDerivAt x (A (x t) + b t) t) ∧
    ∀ y : ℝ → E, y t₀ = x₀ → (∀ t, HasDerivAt y (A (y t) + b t) t) → y = x := by
-- proof
  apply ODE.DuhamelWanted.duhamel_variation_of_constants A b t₀ x₀ hb

-- created on 2026-10-10
