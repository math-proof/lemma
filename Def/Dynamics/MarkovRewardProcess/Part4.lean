import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Def.Probability.Process.MarkovChainTrajectory.Part2
import Lemma.Matrix.Any_And_Stationary.of.RowStochastic
import Lemma.Matrix.Sum_Mul.eq.One.of.StochasticVec.RowStochastic
import Instance.Dynamics.MarkovRewardProcess.Part3
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


namespace FiniteMRP

variable {S : Type u} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
  (MRP : FiniteMRP S)

section stationary

variable [Nonempty S]

-- D = diag μ (rl: `FiniteMRP.D`)
noncomputable def D : Matrix S S ℝ :=
  Matrix.diagonal MRP.μ

-- K = D (γ P - 1) (rl: `FiniteMRP.K`)
noncomputable def K : Matrix S S ℝ :=
  MRP.D * (MRP.γ • MRP.P - 1)

-- chain on pairs drawing (s, s') i.i.d. from μ(s) P(s, s') (rl: `FiniteMRP.aug_chain_iid`)
noncomputable def aug_chain_iid : HomMarkovChainSpec (S × S) where
  kernel := Kernel.const (S × S) (pair_pmf MRP.μ MRP.P).toMeasure
  markov_kernel := inferInstance
  init := ⟨(pair_pmf MRP.μ MRP.P).toMeasure, inferInstance⟩

-- path law of the i.i.d. pair chain (rl: `FiniteMRP.iid_samples`)
noncomputable def iid_samples : Measure (ℕ → S × S) :=
  (MRP.aug_chain_iid.traj_prob : Measure (ℕ → S × S))

end stationary

-- chain on consecutive pairs (s, s') → (s', s'') of the MRP started from p₀ (rl: `FiniteMRP.aug_chain_markov`)
noncomputable def aug_chain_markov : HomMarkovChainSpec (S × S) where
  kernel := Kernel.ofFunOfCountable fun y =>
    (PMF.ofFintype (fun z => ENNReal.ofReal (if y.2 = z.1 then MRP.P z.1 z.2 else 0)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg fun z _ => by
        split_ifs
        · exact (RowStochastic.stochastic z.1).nonneg z.2
        · exact le_rfl]
      simp [Fintype.sum_prod_type, (RowStochastic.stochastic (P := MRP.P) y.2).rowsum])).toMeasure
  markov_kernel := ⟨fun _ => PMF.toMeasure.isProbabilityMeasure _⟩
  init := ⟨(pair_pmf MRP.p₀ MRP.P).toMeasure, inferInstance⟩

-- path law of the pair chain (rl: `FiniteMRP.markov_samples`)
noncomputable def markov_samples : Measure (ℕ → S × S) :=
  (MRP.aug_chain_markov.traj_prob : Measure (ℕ → S × S))

end FiniteMRP
