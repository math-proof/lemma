import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Def.Dynamics.MarkovRewardProcess.Part4
import Def.Dynamics.MarkovDecisionProcess.Part2
open MeasureTheory ProbabilityTheory

universe u v

/-!
# Markov decision processes

Ported from rl-theory-in-lean `RLTheory/MarkovDecisionProcess/MarkovDecisionProcess.lean`.

* `MDPSpec S A`: initial distribution `p₀`, transition law `P (s, a)`, reward `r` and discount `γ`.
* `MDPSpec.pi_kernel pi`, `MDPSpec.pi_kernel₁ pi`: a stationary policy `pi : S → ProbabilityMeasure A`
  as a Markov kernel `S → A`, resp. `(S × A) × S → A` (reading the last state).
* `MDPSpec.transition_kernel`: `P` as a Markov kernel `S × A → S`.
* `MDPSpec.induced_chain pi`: the Markov chain on state–action pairs induced by `pi`.
* `FiniteMDP S A`: an MDP on finite spaces with a policy whose induced chain is irreducible and
  aperiodic and `γ ∈ [0, 1)`; `FiniteMDP.MRP` is the induced `FiniteMRP (S × A)`.
-/


namespace MDPSpec

variable {S : Type u} {A : Type v} [MeasurableSpace S] [MeasurableSpace A]
  [Countable S] [MeasurableSingletonClass S]

instance (pi : S → ProbabilityMeasure A) : IsMarkovKernel (pi_kernel₁ pi) :=
  inferInstanceAs (IsMarkovKernel ((pi_kernel pi).comap Prod.snd measurable_snd))

end MDPSpec
