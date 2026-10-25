import Mathlib
/-! Some finite probability theory -/


namespace ProbabilityTheory

class FinitelyAdditive (A:Type*) [BooleanAlgebra A] where
  prob : A → ℝ
  prob_top : prob ⊤ = 1
  prob_nonneg (E:A) : 0 ≤ prob E
  prob_disj_sup {E F:A} (hEF: Disjoint E F) : prob (E ⊔ F) = prob E + prob F

end ProbabilityTheory
