/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/FieldTheory/Finite/PermutationPolynomial.lean -/

module

public import Def.FieldTheory.Finite.PermutationPolynomial
public import Theorem.Polynomial.Finite.PermutationPolynomial
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

/-- `5` is prime, so `ZMod 5` is a field. -/
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

