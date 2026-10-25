/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Matroid/Algebraic.lean -/


import Def.Combinatorics.Matroid.Algebraic.Part2
import Lemma.Finset.Matroid.Algebraic
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.Algebra.Field.ZMod


namespace AlgebraicMatroidTest

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

end AlgebraicMatroidTest
