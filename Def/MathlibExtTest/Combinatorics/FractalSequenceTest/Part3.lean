/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/FractalSequenceTest.lean -/


import Structure.Combinatorics.FractalSequence
import Lemma.Finset.FractalSequence
import Mathlib.Tactic
import Theorem.MathlibExtTest.Combinatorics.FractalSequenceTest.Part3


namespace MetaMathlibExt

def diagUnpair : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | n + 1 =>
      let p := diagUnpair n
      if p.2 = 0 then (0, p.1 + 1) else (p.1 + 1, p.2 - 1)

end MetaMathlibExt
