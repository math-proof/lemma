import Mathlib
import Abbrev.Analysis.MeasureTheory.Notation.Part3


theorem EuclideanSpace'.norm_eq {n:ℕ} (x: EuclideanSpace' n) : ‖x‖ = √(∑ i, (x i)^2) := by
  convert EuclideanSpace.norm_eq x using 3 with i
  simp

/-- Each coordinate of a Euclidean vector is bounded by its norm. -/
lemma EuclideanSpace'.coord_le_norm {d : ℕ} (x : EuclideanSpace' d) (i : Fin d) :
    |x i| ≤ ‖x‖ := by
  have h1 : (x i)^2 ≤ ∑ j, (x j)^2 :=
    Finset.single_le_sum (f := fun j => (x j)^2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  rw [EuclideanSpace'.norm_eq, (Real.sqrt_sq_eq_abs _).symm]
  exact Real.sqrt_le_sqrt h1

