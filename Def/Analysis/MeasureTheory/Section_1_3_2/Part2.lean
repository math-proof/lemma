import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
import Mathlib.Algebra.Order.Floor.Semifield
import Theorem.Analysis.MeasureTheory.Section_1_3_2
set_option doc.verso.suggestions false


namespace UnsignedMeasurable.TFAE_helpers

variable {d : ℕ} {f : EuclideanSpace' d → EReal}

-- The limsup set for (iii) ⟹ (v)
private def limsupSet (g : ℕ → EuclideanSpace' d → EReal) (t : EReal) : Set (EuclideanSpace' d) :=
  ⋃ (M : ℕ), ⋂ (N : ℕ), ⋃ n ∈ {n | n ≥ N}, {x | g n x > t + 1 / (M + 1)}

end UnsignedMeasurable.TFAE_helpers
