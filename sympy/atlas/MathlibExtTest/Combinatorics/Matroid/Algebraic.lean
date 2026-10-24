/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Matroid/Algebraic.lean -/


import sympy.atlas.Combinatorics.Matroid.Algebraic
import Lemma.Finset.Matroid.Algebraic
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.Algebra.Field.ZMod

namespace AlgebraicMatroidTest

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private def testMatroid : Matroid ℚ :=
  (AlgebraicIndependent.matroid ℚ ℚ).comapOn Set.univ id

private theorem generates_id :
    IntermediateField.adjoin ℚ ((id : ℚ → ℚ) '' Set.univ) = ⊤ := by
  rw [Set.image_id]
  exact IntermediateField.adjoin_univ ℚ ℚ

private def repId : Matroid.AlgebraicRepresentation ℚ testMatroid where
  L := ℚ
  realize := id
  generates := generates_id
  matroid_eq := rfl

private def repSomeId : Matroid.AlgebraicRepresentationSomeField testMatroid where
  K := ℚ
  L := ℚ
  realize := id
  generates := generates_id
  matroid_eq := rfl

example : Matroid.IsAlgebraicOver ℚ testMatroid :=
  repId.toIsAlgebraicOver

example : Matroid.IsAlgebraic testMatroid :=
  repSomeId.toIsAlgebraic

example : testMatroid =
    (AlgebraicIndependent.matroid ℚ ℚ).comapOn testMatroid.E repId.realize :=
  repId.matroid_eq

private noncomputable def testMatroidTrans : Matroid (RatFunc (ZMod 2)) :=
  (AlgebraicIndependent.matroid (ZMod 2) (RatFunc (ZMod 2))).comapOn Set.univ id

private theorem generates_id_trans :
    IntermediateField.adjoin (ZMod 2)
      ((id : RatFunc (ZMod 2) → RatFunc (ZMod 2)) '' testMatroidTrans.E) = ⊤ := by
  have hE : testMatroidTrans.E = Set.univ := rfl
  rw [hE, Set.image_id]
  exact IntermediateField.adjoin_univ (ZMod 2) (RatFunc (ZMod 2))

private noncomputable def repTrans :
    Matroid.AlgebraicRepresentation (ZMod 2) testMatroidTrans where
  L := RatFunc (ZMod 2)
  realize := id
  generates := generates_id_trans
  matroid_eq := rfl

private noncomputable def repSomeTrans :
    Matroid.AlgebraicRepresentationSomeField testMatroidTrans where
  K := ZMod 2
  L := RatFunc (ZMod 2)
  realize := id
  generates := generates_id_trans
  matroid_eq := rfl

example : Transcendental (ZMod 2) (RatFunc.X : RatFunc (ZMod 2)) :=
  RatFunc.transcendental_X

example : Matroid.IsAlgebraicOver (ZMod 2) testMatroidTrans :=
  repTrans.toIsAlgebraicOver

example : Matroid.IsAlgebraic testMatroidTrans :=
  repSomeTrans.toIsAlgebraic

example : testMatroidTrans =
    (AlgebraicIndependent.matroid (ZMod 2) (RatFunc (ZMod 2))).comapOn
      testMatroidTrans.E repTrans.realize :=
  repTrans.matroid_eq

example {K : Type*} [Field K] {E : Type*} {M : Matroid E}
    (R : Matroid.AlgebraicRepresentation K M) : Field R.L :=
  inferInstance

example {K : Type*} [Field K] {E : Type*} {M : Matroid E}
    (R : Matroid.AlgebraicRepresentation K M) : Algebra K R.L :=
  inferInstance

example {K : Type*} [Field K] {E : Type*} {M : Matroid E}
    (R : Matroid.AlgebraicRepresentation K M) : FaithfulSMul K R.L :=
  inferInstance

example {E : Type*} {M : Matroid E}
    (R : Matroid.AlgebraicRepresentationSomeField M) : Field R.K :=
  inferInstance

example {E : Type*} {M : Matroid E}
    (R : Matroid.AlgebraicRepresentationSomeField M) : Field R.L :=
  inferInstance

example {E : Type*} {M : Matroid E}
    (R : Matroid.AlgebraicRepresentationSomeField M) : Algebra R.K R.L :=
  inferInstance

example {E : Type*} {M : Matroid E}
    (R : Matroid.AlgebraicRepresentationSomeField M) : FaithfulSMul R.K R.L :=
  inferInstance

end AlgebraicMatroidTest
