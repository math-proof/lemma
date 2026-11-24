module
public import Structure.Combinatorics.FractalSequence
public import Theorem.Finset.FractalSequence
public import Mathlib.Tactic
public import Theorem.MathlibExtTest.Combinatorics.FractalSequenceTest.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/FractalSequenceTest.lean -/
namespace MetaMathlibExt

def diagPos (i j : ℕ) : ℕ := triangle (i + j) + i

end MetaMathlibExt
