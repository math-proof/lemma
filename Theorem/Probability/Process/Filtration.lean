import Mathlib.Probability.Process.Filtration
import Def.Probability.Process.Filtration
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
theorem shift_apply (ℱ : Filtration ℕ m₀) (n t : ℕ) : ℱ.shift n t = ℱ (t + n) := rfl

end MeasureTheory.Filtration
