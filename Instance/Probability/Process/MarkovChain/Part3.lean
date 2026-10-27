import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Order.Interval.Finset.Nat
import Instance.Probability.Process.StochasticProcessTypes.Part3
import Lemma.Random.Sum_ToReal.eq.One
import Def.Probability.Process.MarkovChain.Part2
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

instance (M : HomMarkovChainSpec S) : StochasticVec M.init_vec where
  nonneg _ := ENNReal.toReal_nonneg
  rowsum := Random.Sum_ToReal.eq.One

instance (M : HomMarkovChainSpec S) : RowStochastic M.kernel_mat where
  stochastic s :=
    have := M.markov_kernel
    { nonneg := fun _ => ENNReal.toReal_nonneg
      rowsum := Random.Sum_ToReal.eq.One (μ := M.kernel s) }

end HomMarkovChainSpec
