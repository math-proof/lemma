import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Order.Interval.Finset.Nat
import Instance.Probability.Process.StochasticProcessTypes.Part3
import Lemma.Random.Sum_ToReal.eq.One
import Instance.Probability.Process.MarkovChain.Part2
open MeasureTheory ProbabilityTheory Finset

universe u

/-!
# Time-homogeneous Markov chains on a measurable state space

Kernel-based counterpart of the finite `DiscreteMarkovChain` primitives in
`Instance.Probability.Process.StochasticProcessTypes.Part3`, ported from rl-theory-in-lean
(`RLTheory/Probability/MarkovChain/Defs.lean`, `.../Finite/Defs.lean`,
`RLTheory/Probability/Kernel/Basic.lean`, `.../Kernel/Composition/MapComap.lean`).

* The `n`-step kernel is Mathlib's monoid power `κ ^ n`
  (`κ ^ (n + 1) = κ ^ n ∘ₖ κ`, `κ ^ 0 = Kernel.id`), which coincides with rl's `Kernel.iter κ n`.
* On a finite state space the one-step kernel and the initial law are read off as a
  `RowStochastic` matrix `M.kernel_mat` and a `StochasticVec` `M.init_vec`.
-/


namespace HomMarkovChainSpec

variable {S : Type u} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

-- one-step transition matrix of a finite chain: `kernel_mat M a b = P(a → b)`
noncomputable def kernel_mat (M : HomMarkovChainSpec S) : Matrix S S ℝ :=
  Matrix.of fun a b => (M.kernel a {b}).toReal

-- initial distribution of a finite chain as a probability vector
noncomputable def init_vec (M : HomMarkovChainSpec S) : S → ℝ :=
  fun s => ((M.init : Measure S) {s}).toReal

end HomMarkovChainSpec
