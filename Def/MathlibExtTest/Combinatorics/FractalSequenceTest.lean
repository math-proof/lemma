/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/FractalSequenceTest.lean -/


import Structure.Combinatorics.FractalSequence
import Lemma.Finset.FractalSequence
import Mathlib.Tactic
import Theorem.MathlibExtTest.Combinatorics.FractalSequenceTest


namespace MetaMathlibExt

/-! ### A concrete regular fractal sequence

The following realizes A002260, Example 5 in the source: concatenate the finite blocks
`(1)`, `(1, 2)`, `(1, 2, 3)`, and so on.  The zero-based position of the `j`th occurrence
of `i + 1` is `triangle (i + j) + i`.
-/

def triangle : ℕ → ℕ
  | 0 => 0
  | n + 1 => triangle n + n + 1

end MetaMathlibExt
