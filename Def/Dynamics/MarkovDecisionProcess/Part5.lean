import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Def.Dynamics.MarkovRewardProcess.Part4
import Structure.Dynamics.MarkovDecisionProcess.Part2
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


namespace FiniteMDP

variable {S : Type u} {A : Type v} [Fintype S] [DecidableEq S] [MeasurableSpace S]
  [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [MeasurableSpace A]
  [MeasurableSingletonClass A]

-- the Markov reward process on state-action pairs induced by the policy (rl: `FiniteMDP.MRP`)
noncomputable def MRP (MDP : FiniteMDP S A) : FiniteMRP (S × A) where
  M := MDP.induced_chain MDP.pi
  hM := MDP.hM
  γ := MDP.γ
  hγ := MDP.hγ
  r := MDP.r

end FiniteMDP
