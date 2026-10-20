import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.LucasBinetFormula
open MetaMathlibExt


/--
[lucas_binet_formulas_of_field](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/LucasBinetFormula.lean)
-/
@[path]
private lemma lucas_binet_formulas_of_field_eq
  [Field K]
  {params : LucasSequenceParams}
  {alpha beta : K}
-- given
  (hsum : alpha + beta = (params.p : K))
  (hprod : alpha * beta = (params.q : K)) :
-- imply
  (alpha ≠ beta → ∀ n : ℕ,
    (lucasU params n : K) = (alpha ^ n - beta ^ n) / (alpha - beta) ∧
    (lucasV params n : K) = alpha ^ n + beta ^ n) ∧
    (beta = alpha → ∀ n : ℕ,
    (lucasU params n : K) = (n : K) * alpha ^ (n - 1) ∧
    (lucasV params n : K) = 2 * alpha ^ n) := by
-- proof
  apply MetaMathlibExt.lucas_binet_formulas_of_field params alpha beta hsum hprod

/--
[lucas_binet_formulas](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/LucasBinetFormula.lean)
-/
@[path]
private lemma lucas_binet_formulas_eq
  [Field K] [CharZero K]
  {params : LucasSequenceParams}
  {alpha beta : K}
-- given
  (hsum : alpha + beta = (params.p : K))
  (hprod : alpha * beta = (params.q : K)) :
-- imply
  (alpha ≠ beta → ∀ n : ℕ,
    (lucasU params n : K) = (alpha ^ n - beta ^ n) / (alpha - beta) ∧
    (lucasV params n : K) = alpha ^ n + beta ^ n) ∧
    (beta = alpha → ∀ n : ℕ,
    (lucasU params n : K) = (n : K) * alpha ^ (n - 1) ∧
    (lucasV params n : K) = 2 * alpha ^ n) := by
-- proof
  apply MetaMathlibExt.lucas_binet_formulas params alpha beta hsum hprod


-- created on 2026-10-20
