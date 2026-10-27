import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Order.Interval.Finset.Nat
import Instance.Probability.Process.StochasticProcessTypes.Part3
import Lemma.Random.Sum_ToReal.eq.One
import Instance.Probability.Process.MarkovChain
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


namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α]

-- apply κ to the last state `h n` of a history `h : Iic n → α`
noncomputable def comap_last (κ : Kernel α α) (n : ℕ) : Kernel (Iic n → α) α :=
  κ.comap (fun h => h ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

end ProbabilityTheory.Kernel
