/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/FractalSequenceTest.lean -/


import Structure.Combinatorics.FractalSequence
import Lemma.Finset.FractalSequence
import Mathlib.Tactic
import Def.MathlibExtTest.Combinatorics.FractalSequenceTest.Part4


namespace MetaMathlibExt

example : diagonalFractal.seq 0 = 1 := rfl

example : diagonalFractal.seq 1 = 1 := rfl

example : diagonalFractal.seq 2 = 2 := rfl

example : diagonalFractal.seq 5 = 3 := rfl

example : diagonalFractal.pos 2 1 = 8 := rfl

end MetaMathlibExt
