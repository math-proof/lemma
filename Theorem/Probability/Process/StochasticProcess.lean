module

public import Instance.Probability.Process.StochasticProcessTypes.Part3
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Theorem.Matrix.L1Norm.eq.One.of.StochasticVec
public import Mathlib.Topology.Instances.Matrix
public import Instance.Probability.Process.StochasticProcess
open Finset WithLp Matrix Filter Metric Bornology Topology Function PiLp
open scoped Topology BigOperators Matrix NNReal
set_option maxHeartbeats 800000

public section

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

