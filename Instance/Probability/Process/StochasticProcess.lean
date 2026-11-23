module

public import Instance.Probability.Process.StochasticProcessTypes.Part3
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Topology.Instances.Matrix
@[expose] public section

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


-- everything in the Simplex space is stochastic
instance (x : Simplex S) : StochasticVec (WithLp.ofLp (x : l1Space S)) :=
  x.property

