/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Tribonacci.lean -/

import Mathlib.Data.List.Basic
import Inductive.Combinatorics.InfiniteWord.Tribonacci
/-!
# The Tribonacci word

This file constructs the finite Tribonacci words and their coherent infinite limit.

The source prints `W(3) = abacabaabacab`, but its stated recurrence makes this word
`W(4)` and gives `W(3) = abacaba`; the definitions below follow the recurrence.

## References

- [E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
  Tribonacci Numbers*](https://cs.uwaterloo.ca/journals/JIS/VOL28/Khovanova/khova43.tex),
  Section 5.1 (source statement `jis_e3c891cabe6bea6b4eecdf73`).
-/


namespace InfiniteWord

/-- Finite Tribonacci-word approximants: `W(0) = a`, `W(1) = ab`, `W(2) = abac`,
and `W(n + 3) = W(n + 2) W(n + 1) W(n)`, where juxtaposition is concatenation. -/
def tribonacciWordApprox : Nat → List TribonacciLetter
  | 0 => [.a]
  | 1 => [.a, .b]
  | 2 => [.a, .b, .a, .c]
  | n + 3 => tribonacciWordApprox (n + 2) ++ tribonacciWordApprox (n + 1) ++
      tribonacciWordApprox n

end InfiniteWord
