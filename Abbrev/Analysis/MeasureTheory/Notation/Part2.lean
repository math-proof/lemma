import Mathlib
import Theorem.Analysis.MeasureTheory.Notation


/-- A version of {name}`EuclideanSpace` suitable for this text. -/
noncomputable abbrev EuclideanSpace' (n: ℕ) := EuclideanSpace ℝ (Fin n)

abbrev EuclideanSpace'.equiv_Real : EuclideanSpace' 1 ≃ ℝ where
  toFun x := x ⟨ 0, by simp ⟩
  invFun x := .toLp 2 (fun _ ↦ x)
  left_inv x := by
    apply PiLp.ext; intro ⟨i, hi⟩; have : i = 0 := by omega
    subst this; rfl
  right_inv x := by rfl

abbrev Real.equiv_EuclideanSpace' : ℝ ≃ EuclideanSpace' 1 := EuclideanSpace'.equiv_Real.symm

