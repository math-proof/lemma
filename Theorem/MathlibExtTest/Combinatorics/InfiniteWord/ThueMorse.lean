/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/ThueMorse.lean -/


import Def.Combinatorics.InfiniteWord.ThueMorse


namespace MetaMathlibExt

example : thueMorseSubstitution false = [false, true] := rfl

example : thueMorseSubstitution true = [true, false] := rfl

example : thueMorseBlock 0 = [false] := rfl

example : thueMorseBlock 1 = [false, true] := rfl

example : thueMorseBlock 2 = [false, true, true, false] := rfl

example : thueMorseBlock 3 = [false, true, true, false, true, false, false, true] := rfl

example : thueMorse 0 = false := rfl

example : thueMorse 1 = true := rfl

example : thueMorse 2 = true := rfl

example : thueMorse 3 = false := rfl

example : thueMorse 7 = true := rfl

example : thueMorse 15 = false := rfl

/-- The direct binary-parity definition agrees with the first four iterations
of the cited substitution construction. -/
example : List.ofFn (fun i : Fin 16 ↦ thueMorse i) = thueMorseBlock 4 := by
  decide

/-- Regression test: evaluating a large index does not materialize a prefix of
the sequence. -/
example : thueMorse 1000000000 = true := rfl

#print axioms thueMorseSubstitution
#print axioms thueMorseBlock
#print axioms thueMorse

end MetaMathlibExt
