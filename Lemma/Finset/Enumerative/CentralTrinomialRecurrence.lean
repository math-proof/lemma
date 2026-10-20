import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.CentralTrinomialRecurrence
open MetaMathlibExt


/--
[centralTrinomialCoeff_three_term_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralTrinomialRecurrence.lean)
-/
@[path]
private lemma centralTrinomialCoeff_three_term_recurrence_eq
  {n : ℕ} :
-- imply
  (n + 1) * trinomialCoefficient (n + 1) (n + 1) =
    (2 * n + 1) * trinomialCoefficient n n +
    3 * n * trinomialCoefficient (n - 1) (n - 1) := by
-- proof
  apply MetaMathlibExt.centralTrinomialCoeff_three_term_recurrence n


-- created on 2026-10-20
