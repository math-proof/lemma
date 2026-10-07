import sympy.stats.markov_reward_process
import sympy.Basic
open Matrix Finset


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {MRP : FiniteMRP S}
-- given
  (x : S → ℝ) :
-- imply
  x ᵥ* MRP.D ⬝ᵥ x = ∑ s, MRP.μ s * x s ^ 2 := by
-- proof
  simp only [FiniteMRP.D, vecMul_diagonal, dotProduct]
  exact sum_congr rfl fun s _ => by ring


-- created on 2026-09-26