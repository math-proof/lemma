import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Restriction
import sympy.vector.euclidean

/-!
# Stochastic-approximation iterates

Ported from rl-theory-in-lean `RLTheory/StochasticApproximation/Iterates.lean`.
These are properties of a given sequence of random vectors, hence `Prop`-valued classes
(following `RobbinsMonro`).

* `Iterates x x₀ f e₁ e₂ α`: `x 0 = x₀`, `x (n+1) = x n + α n (f (x n) - x n) + e₁ (n+1) + e₂ (n+1)`.
* `AdaptedOnSamplePath x`: each `x n` is a measurable function of the first `n + 1` samples
  `frestrictLe n ω`.
* `iterates_update hnm φ φ₁`: the path functional `x ↦ φ (φ₁ (x restricted to [0, n]), x m)` for `n ≤ m`.
* `IteratesOfResidual x x₀ α F`: `x 0 = x₀`, `x (n+1) = x n + α n (F (x n) (ω (n+1)) - x n)` along a
  sample path `ω : ℕ → S × S`.
-/
open Finset MeasureTheory Preorder

variable {d : ℕ}

-- SA iterates with extraneous errors e₁ e₂ (rl: `StochasticApproximation.Iterates`)
class Iterates {Ω : Type*} (x : ℕ → Ω → EuclideanVec d) (x₀ : EuclideanVec d)
    (f : EuclideanVec d → EuclideanVec d) (e₁ e₂ : ℕ → Ω → EuclideanVec d) (α : ℕ → ℝ) : Prop where
  init : ∀ ω, x 0 ω = x₀
  step : ∀ n ω, x (n + 1) ω = x n ω + α n • (f (x n ω) - x n ω) + e₁ (n + 1) ω + e₂ (n + 1) ω

-- x n depends measurably on the first n + 1 samples (rl: `StochasticApproximation.AdaptedOnSamplePath`)
class AdaptedOnSamplePath {S Z : Type*} [MeasurableSpace S] [MeasurableSpace Z]
    (x : ℕ → (ℕ → S) → Z) : Prop where
  property : ∀ n, ∃ xn : (Iic n → S) → Z, Measurable xn ∧ ∀ ω, x n ω = xn (frestrictLe n ω)

-- SA iterates driven by the residual F along a sample path (rl: `StochasticApproximation.IteratesOfResidual`)
class IteratesOfResidual {S : Type*} (x : ℕ → (ℕ → S × S) → EuclideanVec d) (x₀ : EuclideanVec d)
    (α : ℕ → ℝ) (F : EuclideanVec d → S × S → EuclideanVec d) : Prop where
  init : ∀ ω, x 0 ω = x₀
  step : ∀ n ω, x (n + 1) ω = x n ω + α n • (F (x n ω) (ω (n + 1)) - x n ω)

-- ω ↦ φ (φ₁ (ω restricted to [0, n]), ω m) for n ≤ m (rl: `StochasticApproximation.iterates_update`)
def iterates_update {S α β : Type*} {n m : ℕ} (hnm : n ≤ m) (φ : α × S → β) (φ₁ : (Iic n → S) → α) :
    (ℕ → S) → β :=
  fun ω => φ (φ₁ (frestrictLe₂ hnm (frestrictLe m ω)), ω m)
