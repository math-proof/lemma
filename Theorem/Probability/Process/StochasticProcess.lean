import Instance.Probability.Process.StochasticProcessTypes.Part3
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Lp.PiLp
import Lemma.Matrix.L1Norm.eq.One.of.StochasticVec
import Mathlib.Topology.Instances.Matrix
import Instance.Probability.Process.StochasticProcess
open Finset WithLp Matrix Filter Metric Bornology Topology Function PiLp
open scoped Topology BigOperators Matrix NNReal
set_option maxHeartbeats 800000

universe u
variable {S : Type u} [Fintype S]

/-!
# Stochastic processes

Topology of the probability simplex, the Markov operator on it, and related
instances — aligned with
[sympy.stats.stochastic_process](https://github.com/sympy/sympy/blob/master/sympy/stats/stochastic_process.py).

Core typeclasses live in `Instance.Probability.Process.StochasticProcessTypes.Part3`.
-/


omit [Fintype S] in
/-- Evaluation on coordinates is continuous in ℓ¹. -/
theorem continuous_coord (s : S) :
    Continuous fun f : l1Space S => WithLp.ofLp f s :=
  PiLp.continuous_apply (p := (1 : ENNReal)) (β := fun _ : S => ℝ) s

