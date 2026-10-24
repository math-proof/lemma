/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PellLucasSequence.lean -/


import sympy.atlas.NumberTheory.PellLucasSequence
import Lemma.Nat.PellLucasSequence


namespace MetaMathlibExt

example : pellLucasSequence 0 = 1 := pellLucasSequence_zero
example : pellLucasSequence 1 = 1 := pellLucasSequence_one
example : pellLucasSequence 2 = 3 := rfl
example : pellLucasSequence 3 = 7 := rfl
example : pellLucasSequence 4 = 17 := rfl
example : pellLucasSequence 5 = 41 := rfl

example (n : ℕ) :
    pellLucasSequence (n + 2) =
      2 * pellLucasSequence (n + 1) + pellLucasSequence n :=
  pellLucasSequence_succ_succ n

#print axioms MetaMathlibExt.pellLucasSequence
#print axioms MetaMathlibExt.pellLucasSequence_zero
#print axioms MetaMathlibExt.pellLucasSequence_one
#print axioms MetaMathlibExt.pellLucasSequence_succ_succ

end MetaMathlibExt
