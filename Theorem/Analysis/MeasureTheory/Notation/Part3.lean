import Mathlib
import Notation.Analysis.MeasureTheory.Notation


theorem EuclideanSpace'.dot_apply {n:ℕ} (x y: EuclideanSpace' n) : x ⬝ y = ∑ i, (x i)*(y i) := by
  convert PiLp.inner_apply x y using 2 with i
  simp [inner, mul_comm]

