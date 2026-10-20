import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.AngleTrisectionImpossible
open MetaMathlibExt


/--
[angle_trisection_impossible](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/AngleTrisectionImpossible.lean)
-/
@[path]
private lemma angle_trisection_impossible_eq
  :
-- imply
  ∀ (IsConstructible : ℝ → Prop) (IsConstructibleAngle : ℝ → Prop),
    (∀ x : ℝ, IsConstructible x ↔
    ∃ (n : ℕ) (K : Fin (n + 1) → Subfield ℝ),
    K 0 = ⊥ ∧
    x ∈ K (Fin.last n) ∧
    ∀ i : Fin n, K i.castSucc ≤ K i.succ ∧
    ∃ b : ℝ, b ∈ K i.succ ∧ b ^ 2 ∈ K i.castSucc ∧
    ∀ y : ℝ, y ∈ K i.succ →
    ∃ u v : ℝ, u ∈ K i.castSucc ∧ v ∈ K i.castSucc ∧ y = u + b * v) →
    (∀ θ : ℝ, IsConstructibleAngle θ ↔ IsConstructible (Real.cos θ)) →
    Irreducible (8 * (Polynomial.X : Polynomial ℚ) ^ 3 -
    6 * (Polynomial.X : Polynomial ℚ) - 1) ∧
    Polynomial.aeval (Real.cos (Real.pi / 9))
    (8 * (Polynomial.X : Polynomial ℚ) ^ 3 -
    6 * (Polynomial.X : Polynomial ℚ) - 1) = 0 ∧
    ¬ IsConstructible (Real.cos (Real.pi / 9)) ∧
    ¬ ∀ θ : ℝ, IsConstructibleAngle θ → IsConstructibleAngle (θ / 3) := by
-- proof
  apply MetaMathlibExt.angle_trisection_impossible


-- created on 2026-10-20
