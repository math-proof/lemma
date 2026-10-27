import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.InnerProductSpace.Continuous


namespace InnerProductSpace.ToeplitzHausdorffWanted

open scoped _root_.InnerProductSpace

/-- Numerical range `W(A) = { ⟪A x, x⟫_ℂ | ‖x‖ = 1 }` for a bounded operator. -/
noncomputable def numericalRange
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) : Set ℂ :=
  { c : ℂ | ∃ x : E, ‖x‖ = 1 ∧ inner (𝕜 := ℂ) (A x) x = c }

end InnerProductSpace.ToeplitzHausdorffWanted
