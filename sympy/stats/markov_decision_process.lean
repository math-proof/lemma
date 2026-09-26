import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import sympy.stats.markov_reward_process

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
open MeasureTheory ProbabilityTheory

universe u v

-- MDP data (rl: `ReinforcementLearning.MDPSpec`)
structure MDPSpec (S : Type u) (A : Type v) [MeasurableSpace S] [MeasurableSpace A] where
  p₀ : ProbabilityMeasure S
  P : S × A → ProbabilityMeasure S
  r : S × A → ℝ
  γ : ℝ

namespace MDPSpec

variable {S : Type u} {A : Type v} [MeasurableSpace S] [MeasurableSpace A]
  [Countable S] [MeasurableSingletonClass S]

-- a stationary policy as a Markov kernel S → A (rl: `MDPSpec.pi_kernel`)
noncomputable def pi_kernel (pi : S → ProbabilityMeasure A) : Kernel S A :=
  Kernel.ofFunOfCountable fun s => (pi s : Measure A)

instance (pi : S → ProbabilityMeasure A) : IsMarkovKernel (pi_kernel pi) :=
  ⟨fun s => (pi s).prop⟩

-- the policy reading the last state of ((s, a), s') (rl: `MDPSpec.pi_kernel₁`)
noncomputable def pi_kernel₁ (pi : S → ProbabilityMeasure A) : Kernel ((S × A) × S) A :=
  (pi_kernel pi).comap Prod.snd measurable_snd

instance (pi : S → ProbabilityMeasure A) : IsMarkovKernel (pi_kernel₁ pi) :=
  inferInstanceAs (IsMarkovKernel ((pi_kernel pi).comap Prod.snd measurable_snd))

variable [Countable A] [MeasurableSingletonClass A] (M : MDPSpec S A)

-- the transition law as a Markov kernel S × A → S (rl: `MDPSpec.transition_kernel`)
noncomputable def transition_kernel : Kernel (S × A) S :=
  Kernel.ofFunOfCountable fun sa => (M.P sa : Measure S)

instance : IsMarkovKernel M.transition_kernel :=
  ⟨fun sa => (M.P sa).prop⟩

-- the chain on state-action pairs induced by the policy pi (rl: `MDPSpec.induced_chain`)
noncomputable def induced_chain (pi : S → ProbabilityMeasure A) : HomMarkovChainSpec (S × A) where
  kernel := M.transition_kernel ⊗ₖ pi_kernel₁ pi
  markov_kernel := inferInstance
  init := ⟨(M.p₀ : Measure S) ⊗ₘ pi_kernel pi, inferInstance⟩

end MDPSpec

-- a finite MDP with an ergodic policy (rl: `ReinforcementLearning.FiniteMDP`)
structure FiniteMDP (S : Type u) (A : Type v) [Fintype S] [DecidableEq S] [MeasurableSpace S]
    [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [MeasurableSpace A]
    [MeasurableSingletonClass A] extends MDPSpec S A where
  pi : S → ProbabilityMeasure A
  hM : StochasticIrreducible ((MDPSpec.mk p₀ P r γ).induced_chain pi).kernel_mat ∧
    Aperiodic ((MDPSpec.mk p₀ P r γ).induced_chain pi).kernel_mat
  hγ : 0 ≤ γ ∧ γ < 1

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