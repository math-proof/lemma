import Mathlib.Probability.Process.Filtration
import Def.Probability.Process.Filtration.Part2
/-!
# Shifted filtrations

Ported from rl-theory-in-lean `RLTheory/StochasticApproximation/MartingaleDifference.lean`.

* `ℱ.shift n`: the filtration `t ↦ ℱ (t + n)`; it is definitionally `ℱ (t + n)` at time `t`.
* `ℱ.subsequence ht`: the filtration `n ↦ ℱ (t n)` along a monotone time change `t`
  (from `RLTheory/StochasticApproximation/MarkovSamples.lean`).
-/


namespace MeasureTheory.Filtration

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}

@[simp]
theorem subsequence_apply (ℱ : Filtration ℕ m₀) {t : ℕ → ℕ} (ht : Monotone t) (n : ℕ) :
    ℱ.subsequence ht n = ℱ (t n) := rfl

end MeasureTheory.Filtration
