import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.QuadraticGaussSumFive
open scoped MetaMathlibExt
open MetaMathlibExt


/--
[quadraticGaussSum5_eval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticGaussSumFive.lean)
-/
@[path]
private lemma quadraticGaussSum5_eval_eq
  {k : ℤ}
-- given
  (hk : ¬ (5 : ℤ) ∣ k) :
-- imply
  quadraticGaussSum5 k =
    ((legendreSym 5 k : ℤ) : ℂ) * ((Real.sqrt 5 : ℝ) : ℂ) := by
-- proof
  apply MetaMathlibExt.quadraticGaussSum5_eval k hk


-- created on 2026-10-20
