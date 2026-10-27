import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Instance.Probability.Process.MarkovChain.Part3
open MeasureTheory ProbabilityTheory Finset

universe u

/-!
# Trajectory measure of a time-homogeneous Markov chain

Ported from rl-theory-in-lean `RLTheory/Probability/MarkovChain/Trajectory.lean`.
The path space is `ℕ → S` (rl's `X S n := S` is inlined as `fun _ => S`), the history-dependent
kernels are `M.kernel.comap_last n`, and the law of the whole path is Mathlib's Ionescu-Tulcea
`Kernel.trajMeasure` started from `M.init`.
-/


namespace HomMarkovChainSpec

variable {S : Type u} [MeasurableSpace S]

-- step-n kernel of the chain seen as a kernel on histories `Iic n → S` (only the last state matters)
noncomputable def expand_kernel (M : HomMarkovChainSpec S) (n : ℕ) : Kernel (Iic n → S) S :=
  M.kernel.comap_last n

end HomMarkovChainSpec
