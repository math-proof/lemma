/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PellNumberSequence.lean -/


import sympy.atlas.NumberTheory.PellNumberSequence


namespace MetaMathlibExt

example : pellNumber 0 = 0 := rfl
example : pellNumber 1 = 1 := rfl
example : pellNumber 2 = 2 := rfl
example : pellNumber 3 = 5 := rfl
example : pellNumber 4 = 12 := rfl
example : pellNumber 5 = 29 := rfl

example (n : ℕ) :
    pellNumber (n + 2) = 2 * pellNumber (n + 1) + pellNumber n := rfl

#print axioms MetaMathlibExt.pellNumber

end MetaMathlibExt
