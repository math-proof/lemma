import Mathlib.Data.Matrix.Basic
import Abbrev.Analysis.Real.Relational
import Theorem.Analysis.Real.Relational


/-- Entrywise hyperreal closeness, the matrix form of `XEq (Tensor α s)`. -/
instance [XEq α] : XEq (Matrix m n α) where
  r A B := ∀ i j, A i j ≈ B i j
  iseqv :=
    {
      refl _ := by intro i j; rfl
      symm h := by intro i j; exact (h i j).symm
      trans h₁ h₂ := by intro i j; exact (h₁ i j).trans (h₂ i j)
    }


instance [Coe α β] : Coe (Matrix m n α) (Matrix m n β) where
  coe A := Matrix.of fun i j => (A i j : β)
