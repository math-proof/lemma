module
public import Structure.Combinatorics.FractalSequence
public import Theorem.Finset.FractalSequence
public import Mathlib.Tactic
public import Def.MathlibExtTest.Combinatorics.FractalSequenceTest.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/FractalSequenceTest.lean -/
namespace MetaMathlibExt

example : diagonalFractal.seq 0 = 1 := rfl

example : diagonalFractal.seq 1 = 1 := rfl

example : diagonalFractal.seq 2 = 2 := rfl

example : diagonalFractal.seq 5 = 3 := rfl

example : diagonalFractal.pos 2 1 = 8 := rfl

end MetaMathlibExt
