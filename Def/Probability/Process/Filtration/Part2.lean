import Mathlib.Probability.Process.Filtration
import Theorem.Probability.Process.Filtration
/-!
# Shifted filtrations

Ported from rl-theory-in-lean `RLTheory/StochasticApproximation/MartingaleDifference.lean`.

* `ℱ.shift n`: the filtration `t ↦ ℱ (t + n)`; it is definitionally `ℱ (t + n)` at time `t`.
* `ℱ.subsequence ht`: the filtration `n ↦ ℱ (t n)` along a monotone time change `t`
  (from `RLTheory/StochasticApproximation/MarkovSamples.lean`).
-/


namespace MeasureTheory.Filtration

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}

-- the filtration along a monotone time change: n ↦ ℱ (t n) (rl: `MeasureTheory.Filtration.subsequence`)
def subsequence (ℱ : Filtration ℕ m₀) {t : ℕ → ℕ} (ht : Monotone t) : Filtration ℕ m₀ where
  seq n := ℱ (t n)
  mono' _ _ h := ℱ.mono (ht h)
  le' n := ℱ.le (t n)

end MeasureTheory.Filtration
