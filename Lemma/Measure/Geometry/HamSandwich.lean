import Mathlib
import sympy.Basic
import sympy.atlas.MeasureTheory.Geometry.HamSandwich
open MeasureTheory
open Metric
open scoped InnerProductSpace MeasureTheory
open MathlibExt.MeasureTheory.Geometry.HamSandwichWanted


/--
[ham_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/HamSandwich.lean)
-/
@[path]
private lemma ham_sandwich_eq
  {n : ℕ} [MeasurableSpace (EuclideanSpace ℝ (Fin n))] [BorelSpace (EuclideanSpace ℝ (Fin n))]
  {μ : Fin n → Measure (EuclideanSpace ℝ (Fin n))}
-- given
  (hn : 0 < n)
  (hfin : ∀ i, IsFiniteMeasure (μ i))
  (hac : ∀ i, μ i ≪ volume) :
-- imply
  ∃ (v : EuclideanSpace ℝ (Fin n)) (t : ℝ), ‖v‖ = 1 ∧
    ∀ i : Fin n, μ i {x | ⟪v, x⟫_ℝ ≤ t} = μ i Set.univ / 2 ∧
    μ i {x | ⟪v, x⟫_ℝ ≥ t} = μ i Set.univ / 2 := by
-- proof
  apply MathlibExt.MeasureTheory.Geometry.HamSandwichWanted.ham_sandwich hn μ hfin hac


-- created on 2026-10-20
