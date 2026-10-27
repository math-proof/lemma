import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Restriction
import Abbrev.Analysis.InnerProductSpace.EuclideanVec
import Class.Dynamics.Iterates
open Finset MeasureTheory Preorder

variable {d : ℕ}

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


-- ω ↦ φ (φ₁ (ω restricted to [0, n]), ω m) for n ≤ m (rl: `StochasticApproximation.iterates_update`)
def iterates_update {S α β : Type*} {n m : ℕ} (hnm : n ≤ m) (φ : α × S → β) (φ₁ : (Iic n → S) → α) :
    (ℕ → S) → β :=
  fun ω => φ (φ₁ (frestrictLe₂ hnm (frestrictLe m ω)), ω m)

