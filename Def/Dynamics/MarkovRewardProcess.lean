import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Def.Probability.Process.MarkovChainTrajectory.Part2
import Lemma.Matrix.Any_And_Stationary.of.RowStochastic
import Lemma.Matrix.Sum_Mul.eq.One.of.StochasticVec.RowStochastic
import Structure.Dynamics.MarkovRewardProcess
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


-- the law of a transition pair (s, s') with s ~ x and s' ~ P s
noncomputable def pair_pmf {S : Type u} [Fintype S] (x : S → ℝ) [hx : StochasticVec x]
    (P : Matrix S S ℝ) [hP : RowStochastic P] : PMF (S × S) :=
  PMF.ofFintype (fun y => ENNReal.ofReal (x y.1 * P y.1 y.2)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun y _ =>
      mul_nonneg (hx.nonneg y.1) ((hP.stochastic y.1).nonneg y.2), Fintype.sum_prod_type,
      Matrix.Sum_Mul.eq.One.of.StochasticVec.RowStochastic hP hx, ENNReal.ofReal_one])

namespace FiniteMRP

variable {S : Type u} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
  (MRP : FiniteMRP S)

-- transition matrix (rl: `FiniteMRP.P`)
noncomputable def P : Matrix S S ℝ :=
  MRP.M.kernel_mat

end FiniteMRP
