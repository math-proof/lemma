import Mathlib
import sympy.Basic
import sympy.Analysis.Complex.SchwarzReflection

open Complex.SchwarzReflection

/--
[schwarz_reflection](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/SchwarzReflection.lean)
-/
@[path]
private lemma schwarz_reflection_eq
-- given
  (f : ℂ → ℂ)
  (hf1 : DifferentiableOn ℂ f {z | 0 < z.im})
  (hf2 : ContinuousOn f {z | 0 ≤ z.im})
  (h3 : ∀ z : ℂ, z.im = 0 → (f z).im = 0) :
-- imply
  ∃ g : ℂ → ℂ,
    DifferentiableOn ℂ g Set.univ ∧
      (∀ z : ℂ, 0 ≤ z.im → g z = f z) ∧
        ∀ z : ℂ, g (star z) = star (g z) := by
-- proof
  apply schwarz_reflection f hf1 hf2 h3


-- created on 2026-10-10
