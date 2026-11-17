module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Structure.Probability.Process.MarkovChain
public import Class.Probability.Process.StochasticProcessTypes.Part2
public import Class.Probability.Process.StochasticProcessTypes.Part3
public import Def.Probability.Process.MarkovChain.Part2
public import Instance.Probability.Process.MarkovChain.Part3
public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal Matrix

universe u

/-!
# Finite Markov reward processes

Ported from rl-theory-in-lean `RLTheory/MarkovDecisionProcess/MarkovRewardProcess.lean`.

* `FiniteMRP S`: a time-homogeneous Markov chain `M` on a finite state space whose transition
  matrix is irreducible and aperiodic, a discount factor `γ ∈ [0, 1)` and a reward `r : S → ℝ`.
  Data and its side conditions are bundled in one structure, following `Anchors`.
* `MRP.P`, `MRP.p₀`: the transition matrix and the initial distribution (with their
  `RowStochastic` / `StochasticIrreducible` / `Aperiodic` / `StochasticVec` instances).
* `MRP.μ`: a stationary distribution of `MRP.P` (chosen; it is unique by
  `Matrix.Any_And_Stationary.of.StochasticIrreducible.Aperiodic`), `MRP.D = diag μ`,
  `MRP.K = D (γ P - 1)`.
* `MRP.aug_chain_iid` / `MRP.aug_chain_markov`: Markov chains on pairs `(s, s')` drawing
  transitions i.i.d. from `μ(s) P(s, s')`, resp. along the chain started from `p₀`;
  `MRP.iid_samples` / `MRP.markov_samples` are their path laws.
-/


-- a finite Markov reward process (rl: `ReinforcementLearning.FiniteMRP`)
structure FiniteMRP (S : Type u) [Fintype S] [DecidableEq S]
    [MeasurableSpace S] [MeasurableSingletonClass S] where
  M : HomMarkovChainSpec S
  hM : StochasticIrreducible M.kernel_mat ∧ Aperiodic M.kernel_mat
  γ : ℝ
  hγ : 0 ≤ γ ∧ γ < 1
  r : S → ℝ

