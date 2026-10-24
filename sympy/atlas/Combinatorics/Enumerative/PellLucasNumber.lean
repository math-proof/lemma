/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PellLucasNumber.lean -/

import Mathlib.Data.Nat.Basic

namespace MetaMathlibExt

/-!
# Pell--Lucas numbers

Source: K. Kaygisiz and A. Şahin, *Generalized Bivariate Lucas p-Polynomials and Hessenberg
Matrices*, Journal of Integer Sequences 15 (2012),
[`kaygisiz3.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL15/Kaygisiz/kaygisiz3.tex).
-/

/-- The Pell--Lucas sequence, initialized by `Q₀ = Q₁ = 2` and satisfying
`Qₙ₊₂ = 2 Qₙ₊₁ + Qₙ`. This is the source's specialization
`L_{1,n}(2,1)`. -/
def pellLucas : Nat → Nat
  | 0 => 2
  | 1 => 2
  | n + 2 => 2 * pellLucas (n + 1) + pellLucas n
end MetaMathlibExt
