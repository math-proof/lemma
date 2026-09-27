import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Order.Interval.Finset.Nat
import sympy.stats.stochastic_process_types
import Lemma.Random.Sum_ToReal.eq.One

/-!
# Time-homogeneous Markov chains on a measurable state space

Kernel-based counterpart of the finite `DiscreteMarkovChain` primitives in
`sympy.stats.stochastic_process_types`, ported from rl-theory-in-lean
(`RLTheory/Probability/MarkovChain/Defs.lean`, `.../Finite/Defs.lean`,
`RLTheory/Probability/Kernel/Basic.lean`, `.../Kernel/Composition/MapComap.lean`).

* The `n`-step kernel is Mathlib's monoid power `κ ^ n`
  (`κ ^ (n + 1) = κ ^ n ∘ₖ κ`, `κ ^ 0 = Kernel.id`), which coincides with rl's `Kernel.iter κ n`.
* On a finite state space the one-step kernel and the initial law are read off as a
  `RowStochastic` matrix `M.kernel_mat` and a `StochasticVec` `M.init_vec`.
-/
open MeasureTheory ProbabilityTheory Finset

universe u

-- a time-homogeneous Markov chain: a Markov transition kernel and an initial distribution
structure HomMarkovChainSpec (S : Type u) [MeasurableSpace S] where
  kernel : Kernel S S
  markov_kernel : IsMarkovKernel kernel
  init : ProbabilityMeasure S

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α]

-- the n-step transition kernel of a Markov kernel is Markov (rl: instance on `κ.iter n`)
instance IsMarkovKernel.pow (κ : Kernel α α) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (κ ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact inferInstanceAs (IsMarkovKernel Kernel.id)
  | succ n ih =>
    rw [pow_succ]
    exact IsMarkovKernel.comp (κ ^ n) κ

-- apply κ to the last state `h n` of a history `h : Iic n → α`
noncomputable def comap_last (κ : Kernel α α) (n : ℕ) : Kernel (Iic n → α) α :=
  κ.comap (fun h => h ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

instance (κ : Kernel α α) [IsMarkovKernel κ] (n : ℕ) : IsMarkovKernel (κ.comap_last n) :=
  IsMarkovKernel.comap κ (measurable_pi_apply _)

end ProbabilityTheory.Kernel

namespace HomMarkovChainSpec

variable {S : Type u} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

-- one-step transition matrix of a finite chain: `kernel_mat M a b = P(a → b)`
noncomputable def kernel_mat (M : HomMarkovChainSpec S) : Matrix S S ℝ :=
  Matrix.of fun a b => (M.kernel a {b}).toReal

-- initial distribution of a finite chain as a probability vector
noncomputable def init_vec (M : HomMarkovChainSpec S) : S → ℝ :=
  fun s => ((M.init : Measure S) {s}).toReal

instance (M : HomMarkovChainSpec S) : StochasticVec M.init_vec where
  nonneg _ := ENNReal.toReal_nonneg
  rowsum := Random.Sum_ToReal.eq.One

instance (M : HomMarkovChainSpec S) : RowStochastic M.kernel_mat where
  stochastic s :=
    have := M.markov_kernel
    { nonneg := fun _ => ENNReal.toReal_nonneg
      rowsum := Random.Sum_ToReal.eq.One (μ := M.kernel s) }

end HomMarkovChainSpec