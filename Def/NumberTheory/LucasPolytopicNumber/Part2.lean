/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasPolytopicNumber.lean -/

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Real.Basic
import Structure.NumberTheory.LucasPolytopicNumber
open scoped BigOperators

/-!
# Lucas-polytopic numbers

This file formalizes the definitions in Orozco López,
*Simplicial d-Polytopic Numbers Defined on Lucas Sequences*:
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Orozco/oroz2.tex>.
-/


namespace MetaMathlibExt

/-- The Lucas bracket sequence with initial values zero and one and recurrence
`{n + 2}ₛₜ = s * {n + 1}ₛₜ + t * {n}ₛₜ`. -/
def lucasBracket (P : LucasParameters) : ℕ → ℝ
  | n => lucasBracketAux P.s P.t n

/-- The `s,t`-factorial, the product of Lucas brackets from one through `n`. -/
def lucasFactorial (P : LucasParameters) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, lucasBracket P (k + 1)

/-- The Lucasnomial coefficient. As for `Nat.choose`, it is zero when
`k > n`; within its source domain it is the displayed quotient of
`s,t`-factorials. -/
noncomputable def lucasnomial (P : LucasParameters) (n k : ℕ) : ℝ :=
  if k ≤ n then lucasFactorial P n / (lucasFactorial P k * lucasFactorial P (n - k)) else 0

/-- The `n`-th simplicial `d`-Lucas-polytopic number. -/
noncomputable def lucasPolytopicNumber (P : LucasParameters) (n d : ℕ) : ℝ :=
  lucasnomial P (n + d - 1) d

/-- The Lucas analogue of the `n`-th triangular number. -/
noncomputable def lucasTriangularNumber (P : LucasParameters) (n : ℕ) : ℝ :=
  lucasnomial P (n + 1) 2

/-- The Lucas analogue of the `n`-th tetrahedral number. -/
noncomputable def lucasTetrahedralNumber (P : LucasParameters) (n : ℕ) : ℝ :=
  lucasnomial P (n + 2) 3

/-- The Lucas analogue of the `n`-th pentachoron number. -/
noncomputable def lucasPentachoronNumber (P : LucasParameters) (n : ℕ) : ℝ :=
  lucasnomial P (n + 3) 4

/-- The Lucas analogue of the `n`-th hexateron number. -/
noncomputable def lucasHexateronNumber (P : LucasParameters) (n : ℕ) : ℝ :=
  lucasnomial P (n + 4) 5

end MetaMathlibExt
