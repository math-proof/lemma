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
public import Instance.Probability.Process.StochasticProcess.Part2

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


-- Markov operator on the simplex

noncomputable def smat_as_operator (P : Matrix S S ℝ) [RowStochastic P] :
    Simplex S → Simplex S :=
  fun μ =>
    ⟨WithLp.toLp 1 (WithLp.ofLp (μ : l1Space S) ᵥ* P), by
      have : StochasticVec (WithLp.ofLp (μ : l1Space S) ᵥ* P) :=
        inferInstance
      simpa using this⟩

