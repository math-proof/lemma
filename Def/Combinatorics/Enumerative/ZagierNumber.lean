/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierNumber.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
open scoped BigOperators


namespace MetaMathlibExt

/-!
# Domb-type sums and Zagier numbers

Source: G.-R. Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024),
[`zhang9.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL27/Zhang/zhang9.tex).
-/

/-- The source's Domb-type sum
`D(n,r,s,t) = ∑_{k=0}^n choose(n,k)^r choose(2k,k)^s choose(2(n-k),n-k)^t`.
The paper uses positive `r`; the same finite formula is meaningful at `r = 0`. -/
def dombTypeSum (n r s t : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1),
    n.choose k ^ r * (2 * k).choose k ^ s *
      (2 * (n - k)).choose (n - k) ^ t

/-- The Zagier numbers `Z(n) = D(n,1,1,1)` (OEIS A081085). -/
def zagierNumber (n : ℕ) : ℕ :=
  dombTypeSum n 1 1 1

end MetaMathlibExt
