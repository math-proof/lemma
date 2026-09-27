import sympy.vector.euclidean

/-!
# Lyapunov candidates for stochastic approximation

Ported from rl-theory-in-lean `RLTheory/StochasticApproximation/Lyapunov.lean`, where these are
classes; here they are `Prop`-valued structures on `EuclideanVec d` (rl: `E d`).

* `LyapunovCandidate φ φ'`: `φ ≥ 0` vanishing exactly at `0`, `L`-smooth with gradient `φ'`,
  `⟪φ' x, x⟫ = C φ x`, `∑ |φ' x i| |y i| ≤ C √(φ x) √(φ y)`, and `√φ` equivalent to `‖·‖`.
* `DecreaseAlong φ φ' f`: `⟪φ' (x - z), f x - x⟫ ≤ -η φ (x - z)` at every fixed point `z` of `f`.
* `LyapunovFunction φ φ' f`: both.
-/

variable {d : ℕ}

-- rl: `StochasticApproximation.LyapunovCandidate`
structure LyapunovCandidate (φ : EuclideanVec d → ℝ) (φ' : EuclideanVec d → EuclideanVec d) : Prop where
  nonneg : ∀ x, 0 ≤ φ x
  zero : ∀ z, z = 0 ↔ φ z = 0
  smooth : ∃ L, 0 ≤ L ∧ ∀ x y, φ y ≤ φ x + inner ℝ (φ' x) (y - x) + L / 2 * ‖y - x‖ ^ 2
  inner_grad_eq : ∃ C, 0 ≤ C ∧ ∀ x, inner ℝ (φ' x) x = C * φ x
  inner_grad_le' : ∃ C, 0 ≤ C ∧ ∀ x y, ∑ i, |φ' x i| * |y i| ≤ C * √(φ x) * √(φ y)
  norm_le : ∃ C, 0 ≤ C ∧ ∀ x, ‖x‖ ≤ C * √(φ x)
  le_norm : ∃ C, 0 ≤ C ∧ ∀ x, √(φ x) ≤ C * ‖x‖

-- rl: `StochasticApproximation.DecreaseAlong`
structure DecreaseAlong (φ : EuclideanVec d → ℝ) (φ' : EuclideanVec d → EuclideanVec d)
    (f : EuclideanVec d → EuclideanVec d) : Prop where
  decrease : ∃ η, 0 < η ∧ ∀ z, z = f z → ∀ x, inner ℝ (φ' (x - z)) (f x - x) ≤ -η * φ (x - z)

-- rl: `StochasticApproximation.LyapunovFunction`
structure LyapunovFunction (φ : EuclideanVec d → ℝ) (φ' : EuclideanVec d → EuclideanVec d)
    (f : EuclideanVec d → EuclideanVec d) : Prop extends LyapunovCandidate φ φ', DecreaseAlong φ φ' f