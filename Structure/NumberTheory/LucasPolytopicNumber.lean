/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasPolytopicNumber.lean -/

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Real.Basic
import Def.NumberTheory.LucasPolytopicNumber
open scoped BigOperators

/-!
# Lucas-polytopic numbers

This file formalizes the definitions in Orozco López,
*Simplicial d-Polytopic Numbers Defined on Lucas Sequences*:
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Orozco/oroz2.tex>.
-/


namespace MetaMathlibExt

/-- Parameters for which every positive Lucas bracket is nonzero. The final
condition is what makes all factorial quotients below genuine field quotients,
rather than Lean's totalized `0 / 0`. -/
structure LucasParameters where
  s : ℝ
  t : ℝ
  s_ne_zero : s ≠ 0
  t_ne_zero : t ≠ 0
  bracket_ne_zero : ∀ n, n ≠ 0 → lucasBracketAux s t n ≠ 0

end MetaMathlibExt
