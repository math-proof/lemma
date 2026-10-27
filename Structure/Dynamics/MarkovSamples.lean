import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Def.Dynamics.MarkovRewardProcess.Part4
import Def.Dynamics.Iterates
import Def.Dynamics.StepSize.Part2
open MeasureTheory Finset

universe u

/-!
# Stochastic approximation with Markovian samples

Ported from rl-theory-in-lean `RLTheory/StochasticApproximation/MarkovSamples.lean`.

* `Skeleton S d`: the data of an SA scheme `x (n+1) = x n + α n (F (x n) (ω (n+1)) - x n)` driven by
  the pair chain of a finite MRP (`mrp.markov_samples`), with anchors `anc` for the step sizes `α`;
  data and side conditions are bundled in one structure, following `Anchors` / `FiniteMRP`.
* `Skeleton.G w y = F w y - w`, `Skeleton.g = f - id`.
* `Skeleton.e₁`, `Skeleton.e₂₁`, `Skeleton.e₂₂`, `Skeleton.e₂`: the martingale-difference and the
  remainder errors of the iterates observed along the anchor times `anc.t`.
-/


-- bundled data of SA with Markovian samples (rl: `StochasticApproximation.Skeleton`)
structure Skeleton (S : Type u) [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (d : ℕ) where
  F : EuclideanVec d → S × S → EuclideanVec d
  hFm : Measurable F.uncurry
  hFlip : ∃ C, 0 ≤ C ∧ ∀ w w' y, ‖F w y - F w' y‖ ≤ C * ‖w - w'‖
  f : EuclideanVec d → EuclideanVec d
  α : ℕ → ℝ
  anc : Anchors α
  hanc : SufficientlySparse anc
  x : ℕ → (ℕ → S × S) → EuclideanVec d
  x₀ : EuclideanVec d
  hx : IteratesOfResidual x x₀ α F
  mrp : FiniteMRP S
  hfF : ∀ w, f w = ∑ s, ∑ s', (mrp.μ s * mrp.P s s') • F w (s, s')

