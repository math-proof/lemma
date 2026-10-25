/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean -/

import Mathlib.Algebra.FreeAlgebra
import Theorem.NumberTheory.MultipleZeta.Index.Part2
import Lemma.Nat.MultipleZeta.Index


namespace MetaMathlibExt.MultipleZeta

/-- The generator `x` as a word. -/
def xWord : FreeMonoid Bool := FreeMonoid.ofList [false]

/-- The generator `y` as a word. -/
def yWord : FreeMonoid Bool := FreeMonoid.ofList [true]

/-- Positive entries of an index. -/
def Index.pnatEntries : Index → List PNat
  | ⟨_, c⟩ => c.blocks.attach.map fun ⟨n, hm⟩ => ⟨n, c.blocks_pos hm⟩

/-- Auxiliary product of Hoffman blocks for a list of `PNat`. -/
def zWordPNat (l : List PNat) : FreeMonoid Bool :=
  (l.map hoffmanBlock).prod

/-- Hoffman word attached to an index, concatenation of blocks in source order. -/
def zWord (idx : Index) : FreeMonoid Bool :=
  zWordPNat idx.pnatEntries

/-- Monomial in the free algebra attached to an index. -/
noncomputable def zMonomial (idx : Index) : FreeAlgebra ℚ Bool :=
  (FreeAlgebra.equivMonoidAlgebraFreeMonoid :
      FreeAlgebra ℚ Bool ≃ₐ[ℚ] MonoidAlgebra ℚ (FreeMonoid Bool)).symm
    (MonoidAlgebra.single (zWord idx) 1)

/-- Predicate for `H^1`: empty or ends in `y`. -/
def IsHOneWord (w : FreeMonoid Bool) : Prop :=
  w = 1 ∨ ∃ u : FreeMonoid Bool, w = u * yWord

/-- Predicate for `H^0`: empty or begins in `x` and ends in `y`. -/
def IsHZeroWord (w : FreeMonoid Bool) : Prop :=
  w = 1 ∨ ∃ u : FreeMonoid Bool, w = xWord * u * yWord

/-- Word submonoid for `H^1`. -/
def wordSubmonoidHOne : Submonoid (FreeMonoid Bool) where
  carrier := { w | IsHOneWord w }
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, IsHOneWord] at ha hb ⊢
    rcases ha with rfl | ⟨ua, rfl⟩
    · simp only [one_mul]
      exact hb
    · rcases hb with rfl | ⟨ub, rfl⟩
      · simp
      · exact Or.inr ⟨ua * yWord * ub, by simp [mul_assoc]⟩
  one_mem' := Or.inl rfl

/-- Word submonoid for `H^0`. -/
def wordSubmonoidHZero : Submonoid (FreeMonoid Bool) where
  carrier := { w | IsHZeroWord w }
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, IsHZeroWord] at ha hb ⊢
    rcases ha with rfl | ⟨ua, rfl⟩
    · simp only [one_mul]
      exact hb
    · rcases hb with rfl | ⟨ub, rfl⟩
      · simp
      · exact Or.inr ⟨ua * yWord * xWord * ub, by simp [mul_assoc]⟩
  one_mem' := Or.inl rfl

/-- Subalgebra `H^1` of the free algebra. -/
noncomputable def hOne : Subalgebra ℚ (FreeAlgebra ℚ Bool) :=
  ((MonoidAlgebra.mapDomainAlgHom ℚ ℚ wordSubmonoidHOne.subtype).range).comap
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid :
      FreeAlgebra ℚ Bool ≃ₐ[ℚ] MonoidAlgebra ℚ (FreeMonoid Bool)).toAlgHom

/-- Subalgebra `H^0` of the free algebra. -/
noncomputable def hZero : Subalgebra ℚ (FreeAlgebra ℚ Bool) :=
  ((MonoidAlgebra.mapDomainAlgHom ℚ ℚ wordSubmonoidHZero.subtype).range).comap
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid :
      FreeAlgebra ℚ Bool ≃ₐ[ℚ] MonoidAlgebra ℚ (FreeMonoid Bool)).toAlgHom

end MetaMathlibExt.MultipleZeta
