import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import sympy.stats.markov_chain

/-!
# Trajectory measure of a time-homogeneous Markov chain

Ported from rl-theory-in-lean `RLTheory/Probability/MarkovChain/Trajectory.lean`.
The path space is `ℕ → S` (rl's `X S n := S` is inlined as `fun _ => S`), the history-dependent
kernels are `M.kernel.comap_last n`, and the law of the whole path is Mathlib's Ionescu-Tulcea
`Kernel.trajMeasure` started from `M.init`.
-/
open MeasureTheory ProbabilityTheory Finset

universe u

namespace HomMarkovChainSpec

variable {S : Type u} [MeasurableSpace S]

-- step-n kernel of the chain seen as a kernel on histories `Iic n → S` (only the last state matters)
noncomputable def expand_kernel (M : HomMarkovChainSpec S) (n : ℕ) : Kernel (Iic n → S) S :=
  M.kernel.comap_last n

instance (M : HomMarkovChainSpec S) (n : ℕ) : IsMarkovKernel (M.expand_kernel n) :=
  have := M.markov_kernel
  inferInstanceAs (IsMarkovKernel (M.kernel.comap_last n))

-- law of the path started from a fixed history `x₀ : Iic 0 → S`
noncomputable def traj_prob₀ (M : HomMarkovChainSpec S) (x₀ : Iic 0 → S) :
    ProbabilityMeasure (ℕ → S) :=
  ⟨Kernel.traj (X := fun _ => S) M.expand_kernel 0 x₀, inferInstance⟩

-- law of the path started from the initial distribution `M.init`
noncomputable def traj_prob (M : HomMarkovChainSpec S) : ProbabilityMeasure (ℕ → S) :=
  ⟨Kernel.trajMeasure (X := fun _ => S) (M.init : Measure S) M.expand_kernel, inferInstance⟩

end HomMarkovChainSpec