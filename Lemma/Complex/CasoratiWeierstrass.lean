import Mathlib
import sympy.Basic
import sympy.Analysis.Complex.CasoratiWeierstrass

open Complex.CasoratiWeierstrass

/--
[casoratiWeierstrass](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/CasoratiWeierstrass.lean)
-/
@[path]
private lemma casoratiWeierstrass_eq
-- given
  {c : ℂ} {r : ℝ} {f : ℂ → ℂ} (hr : 0 < r)
  (hf : DifferentiableOn ℂ f (Metric.ball c r \ {c}))
  (hess : ¬ MeromorphicAt f c) :
-- imply
  Dense (f '' (Metric.ball c r \ {c})) := by
-- proof
  apply casoratiWeierstrass hr hf hess


-- created on 2026-10-09
