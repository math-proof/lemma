import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.DescartesCircleTheorem
open scoped BigOperators
open MetaMathlibExt


/--
[descartes_circle_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/DescartesCircleTheorem.lean)
-/
@[path]
private lemma descartes_circle_theorem_eq
  {c : Fin 4 → EuclideanSpace ℝ (Fin 2)}
  {r k : Fin 4 → ℝ} :
-- imply
  (∀ i, 0 < r i) →
    (((∀ i j, i ≠ j → dist (c i) (c j) = r i + r j) ∧ ∀ i, k i = 1 / r i) ∨
    ∃ e : Fin 4, k e = -1 / r e ∧ (∀ j, j ≠ e → k j = 1 / r j) ∧
    (∀ j, j ≠ e → dist (c e) (c j) = r e - r j) ∧
    ∀ i j, i ≠ e → j ≠ e → i ≠ j → dist (c i) (c j) = r i + r j) →
    (∑ i : Fin 4, k i) ^ 2 = 2 * ∑ i : Fin 4, k i ^ 2 := by
-- proof
  apply MetaMathlibExt.descartes_circle_theorem c r k


-- created on 2026-10-20
