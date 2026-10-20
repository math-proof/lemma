import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.JohnsonLindenstrauss
open scoped RealInnerProductSpace
open ProbabilityTheory MeasureTheory
open MathlibExt.Geometry.Euclidean.JohnsonLindenstraussWanted


/--
[johnson_lindenstrauss](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma johnson_lindenstrauss_eq
  :
-- imply
  ∃ C : ℝ, C > 0 ∧
    ∀ (ε : ℝ), ε > 0 →
    ∀ (m : ℕ) (N : ℕ), N ≥ 2 →
    ∀ (X : Finset (EuclideanSpace ℝ (Fin m))), X.card = N →
    ∀ (d : ℕ), (d : ℝ) > C * ε⁻¹ ^ 2 * Real.log (N : ℝ) →
    ∃ f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d),
    ∀ x ∈ X, ∀ y ∈ X,
    (1 - ε) * ‖x - y‖ ≤ ‖f x - f y‖ ∧
    ‖f x - f y‖ ≤ (1 + ε) * ‖x - y‖ := by
-- proof
  apply MathlibExt.Geometry.Euclidean.JohnsonLindenstraussWanted.johnson_lindenstrauss


-- created on 2026-10-20
