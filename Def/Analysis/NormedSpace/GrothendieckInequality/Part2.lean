/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Theorem.Analysis.NormedSpace.GrothendieckInequality

@[expose] public section

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
