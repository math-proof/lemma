/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasPolytopicNumber.lean -/

module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Real.Basic

@[expose] public section

open scoped BigOperators

/-!
# Lucas-polytopic numbers

This file formalizes the definitions in Orozco López,
*Simplicial d-Polytopic Numbers Defined on Lucas Sequences*:
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Orozco/oroz2.tex>.
-/


namespace MetaMathlibExt

/-- The Lucas bracket recurrence before imposing the nondegeneracy needed by
quotient formulas. -/
def lucasBracketAux (s t : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | n + 2 => s * lucasBracketAux s t (n + 1) + t * lucasBracketAux s t n

end MetaMathlibExt
