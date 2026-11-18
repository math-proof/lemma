/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Matroid/Algebraic.lean -/

module

public import Def.Combinatorics.Matroid.Algebraic.Part2
public import Theorem.Finset.Matroid.Algebraic
public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

namespace AlgebraicMatroidTest

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

end AlgebraicMatroidTest
