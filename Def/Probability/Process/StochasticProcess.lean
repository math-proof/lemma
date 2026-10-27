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
import Instance.Probability.Process.StochasticProcess.Part2
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

