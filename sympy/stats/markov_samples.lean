import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import sympy.stats.markov_reward_process
import sympy.stats.iterates
import sympy.stats.step_size

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
open MeasureTheory Finset

universe u

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

namespace Skeleton

variable {S : Type u} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S]
  [MeasurableSingletonClass S] {d : ℕ} (sk : Skeleton S d)

-- the residual G w y = F w y - w (rl: `Skeleton.G`)
def G : EuclideanVec d → S × S → EuclideanVec d :=
  fun w y => sk.F w y - w

-- the mean residual g = f - id (rl: `Skeleton.g`)
def g : EuclideanVec d → EuclideanVec d :=
  sk.f - id

-- martingale-difference error along the anchors (rl: `Skeleton.e₁`)
noncomputable def e₁ (n : ℕ) (ω : ℕ → S × S) : EuclideanVec d :=
  ∑ i ∈ Ico (sk.anc.t (n - 1)) (sk.anc.t n), sk.α i • (sk.G (sk.x (sk.anc.t (n - 1)) ω) (ω (i + 1)) -
    sk.mrp.markov_samples[fun ω' => sk.G (sk.x (sk.anc.t (n - 1)) ω') (ω' (i + 1)) | Filtration.piLE (sk.anc.t (n - 1))] ω)

-- error from freezing the iterate at the last anchor (rl: `Skeleton.e₂₁`)
noncomputable def e₂₁ (n : ℕ) (ω : ℕ → S × S) : EuclideanVec d :=
  ∑ i ∈ Ico (sk.anc.t (n - 1)) (sk.anc.t n), sk.α i • (sk.G (sk.x i ω) (ω (i + 1)) - sk.G (sk.x (sk.anc.t (n - 1)) ω) (ω (i + 1)))

-- error from the Markovian (non-stationary) sampling (rl: `Skeleton.e₂₂`)
noncomputable def e₂₂ (n : ℕ) (ω : ℕ → S × S) : EuclideanVec d :=
  ∑ i ∈ Ico (sk.anc.t (n - 1)) (sk.anc.t n), sk.α i • (sk.mrp.markov_samples[fun ω' => sk.G (sk.x (sk.anc.t (n - 1)) ω') (ω' (i + 1)) | Filtration.piLE (sk.anc.t (n - 1))] ω -
    sk.g (sk.x (sk.anc.t (n - 1)) ω))

-- the remainder error e₂ = e₂₁ + e₂₂ (rl: `Skeleton.e₂`)
noncomputable def e₂ (n : ℕ) (ω : ℕ → S × S) : EuclideanVec d :=
  sk.e₂₁ n ω + sk.e₂₂ n ω

end Skeleton