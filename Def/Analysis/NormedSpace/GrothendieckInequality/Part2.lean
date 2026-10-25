/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorem.Analysis.NormedSpace.GrothendieckInequality
open scoped InnerProductSpace


section

namespace FunctionalAnalysis.GrothendieckInequalityWanted

/-- Supremum of `|∑ A ⟪x, y⟫|` over Euclidean unit-ball families. -/
noncomputable def gtBound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sSup { r : ℝ | ∃ d : ℕ, ∃ x : Fin m → EuclideanSpace ℝ (Fin d),
    ∃ y : Fin n → EuclideanSpace ℝ (Fin d),
    (∀ i, ‖x i‖ ≤ 1) ∧ (∀ j, ‖y j‖ ≤ 1) ∧ r = |∑ i, ∑ j, A i j * ⟪x i, y j⟫_ℝ| }

end FunctionalAnalysis.GrothendieckInequalityWanted
end
