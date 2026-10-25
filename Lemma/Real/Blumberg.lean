import Mathlib
import sympy.Basic
import Theorem.Analysis.Calculus.Blumberg.Part5

/--
[blumberg_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Blumberg.lean)
-/
@[path]
private lemma blumberg_theorem_eq :
-- imply
  (∀ f : ℝ → ℝ, ∃ D : Set ℝ, Dense D ∧ ContinuousOn f D) :=
-- proof
  MetaMathlibExt.blumberg_theorem


-- created on 2026-10-09
