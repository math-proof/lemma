import Mathlib.Algebra.Polynomial.Bivariate

/-!
# `eval_simp` tactic macro

Carved from `Lemma.Definitions.Def_WeierstrassCurve_VeluPointMap`.
The simp lemmas are resolved in this module.
Enable it with `open scoped WeierstrassCurve.VeluPointMap`.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.VeluPointMap

/-- `eval_simp` tactic macro. -/
scoped macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_neg, eval_add, eval_sub, eval_mul, eval_pow,
    eval_ofNat, evalEval])

end WeierstrassCurve.VeluPointMap
