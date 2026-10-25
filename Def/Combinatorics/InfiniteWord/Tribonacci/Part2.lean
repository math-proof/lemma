/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Tribonacci.lean -/

import Mathlib.Data.List.Basic
import Theorem.Combinatorics.InfiniteWord.Tribonacci
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

/-- The infinite Tribonacci word, obtained from the coherent chain of finite approximants. -/
def tribonacciWord (k : Nat) : TribonacciLetter :=
  (tribonacciWordApprox k)[k]'(by
    have h := tribonacciWordApprox_length_ge k
    omega)

end InfiniteWord
