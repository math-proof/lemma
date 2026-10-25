import Mathlib
import Theorem.Analysis.MeasureTheory.Notation.Part3


def EuclideanSpace'.prod_equiv (d₁ d₂:ℕ) : EuclideanSpace' (d₁ + d₂) ≃ EuclideanSpace' d₁ × EuclideanSpace' d₂ where
  toFun x :=
    (.toLp 2 (fun ⟨i, hi⟩ => x ⟨i, by omega⟩),
     .toLp 2 (fun ⟨i, hi⟩ => x ⟨i + d₁, by omega⟩))
  invFun x := .toLp 2 (fun ⟨i, hi⟩ =>
    if h : i < d₁ then x.1 ⟨i, h⟩ else x.2 ⟨i - d₁, by omega⟩)
  left_inv x := by
    apply PiLp.ext; intro ⟨i, hi⟩
    simp only
    split
    · rfl
    next h =>
      have := Nat.sub_add_cancel (Nat.not_lt.mp h)
      simp only [this]
  right_inv x := by
    ext ⟨i, hi⟩
    · simp [dite_eq_left hi]
    · simp [show ¬(i + d₁ < d₁) by omega]

def EuclideanSpace'.prod {d₁ d₂:ℕ} (E₁: Set (EuclideanSpace' d₁)) (E₂: Set (EuclideanSpace' d₂)) : Set (EuclideanSpace' (d₁+d₂)) := (EuclideanSpace'.prod_equiv d₁ d₂).symm '' (E₁ ×ˢ E₂)

