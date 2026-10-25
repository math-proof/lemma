/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/FractalSequenceTest.lean -/


import Structure.Combinatorics.FractalSequence
import Lemma.Finset.FractalSequence
import Mathlib.Tactic
import Def.MathlibExtTest.Combinatorics.FractalSequenceTest


namespace MetaMathlibExt

@[simp] theorem triangle_zero : triangle 0 = 0 := rfl

@[simp] theorem triangle_succ (n : ℕ) :
    triangle (n + 1) = triangle n + n + 1 := rfl

end MetaMathlibExt
