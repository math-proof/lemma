module
public import Structure.Combinatorics.FractalSequence
public import Theorem.Finset.FractalSequence
public import Mathlib.Tactic
public import Def.MathlibExtTest.Combinatorics.FractalSequenceTest


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/FractalSequenceTest.lean -/
namespace MetaMathlibExt

@[simp] theorem triangle_zero : triangle 0 = 0 := rfl

@[simp] theorem triangle_succ (n : ℕ) :
    triangle (n + 1) = triangle n + n + 1 := rfl

end MetaMathlibExt
