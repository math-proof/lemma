/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PadovanSequence.lean -/


import sympy.atlas.NumberTheory.PadovanSequence
import Lemma.Nat.PadovanSequence


namespace MetaMathlibExt

example : shiftedPadovanSequence 0 = 1 := rfl
example : shiftedPadovanSequence 1 = 0 := rfl
example : shiftedPadovanSequence 2 = 1 := rfl
example : shiftedPadovanSequence 3 = 1 := rfl
example : shiftedPadovanSequence 4 = 1 := rfl
example : shiftedPadovanSequence 5 = 2 := rfl

example (n : Nat) :
    shiftedPadovanSequence (n + 3) =
      shiftedPadovanSequence (n + 1) + shiftedPadovanSequence n := rfl

#print axioms MetaMathlibExt.shiftedPadovanSequence
#print axioms MetaMathlibExt.shiftedPadovanSequence_zero
#print axioms MetaMathlibExt.shiftedPadovanSequence_one
#print axioms MetaMathlibExt.shiftedPadovanSequence_two
#print axioms MetaMathlibExt.shiftedPadovanSequence_add_three

end MetaMathlibExt
