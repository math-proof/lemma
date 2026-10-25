/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/FractalSequenceTest.lean -/


import Structure.Combinatorics.FractalSequence
import Lemma.Finset.FractalSequence
import Mathlib.Tactic
import Theorem.MathlibExtTest.Combinatorics.FractalSequenceTest.Part2


namespace MetaMathlibExt

def diagPos (i j : ℕ) : ℕ := triangle (i + j) + i

end MetaMathlibExt
