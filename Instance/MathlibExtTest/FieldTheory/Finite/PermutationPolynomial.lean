/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/FieldTheory/Finite/PermutationPolynomial.lean -/


import Def.FieldTheory.Finite.PermutationPolynomial
import Lemma.Polynomial.Finite.PermutationPolynomial
import Mathlib.FieldTheory.Finite.Basic


/-- `5` is prime, so `ZMod 5` is a field. -/
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

