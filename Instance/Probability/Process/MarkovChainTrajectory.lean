module

public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Instance.Probability.Process.MarkovChain.Part2
public import Instance.Probability.Process.MarkovChain.Part3
public import Def.Probability.Process.MarkovChainTrajectory
public import Def.Probability.Process.MarkovChain

/-!
# Trajectory measure of a time-homogeneous Markov chain

Ported from rl-theory-in-lean `RLTheory/Probability/MarkovChain/Trajectory.lean`.
The path space is `ℕ → S` (rl's `X S n := S` is inlined as `fun _ => S`), the history-dependent
kernels are `M.kernel.comap_last n`, and the law of the whole path is Mathlib's Ionescu-Tulcea
`Kernel.trajMeasure` started from `M.init`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

universe u

namespace HomMarkovChainSpec

variable {S : Type u} [MeasurableSpace S]

instance (M : HomMarkovChainSpec S) (n : ℕ) : IsMarkovKernel (M.expand_kernel n) :=
  have := M.markov_kernel
  inferInstanceAs (IsMarkovKernel (M.kernel.comap_last n))

end HomMarkovChainSpec
