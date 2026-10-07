import sympy.stats.markov_reward_process
import sympy.Basic
import Lemma.Matrix.GeometricMixing.of.StochasticIrreducible.Aperiodic
import Lemma.Matrix.Any_And_Stationary.of.StochasticIrreducible.Aperiodic
open Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {MRP : FiniteMRP S} :
-- imply
  ∃ ρ C, 0 < ρ ∧ ρ < 1 ∧ 0 ≤ C ∧ ∀ s n, ∑ s', |(MRP.P ^ n) s s' - MRP.μ s'| ≤ C * ρ ^ n := by
-- proof
  obtain ⟨C, ρ, μ, hC, hρ, hρ1, hμ, hμP, hmix⟩ :=
    (GeometricMixing.of.StochasticIrreducible.Aperiodic (P := MRP.P) inferInstance inferInstance).mixing
  have heq : μ = MRP.μ :=
    (Any_And_Stationary.of.StochasticIrreducible.Aperiodic (P := MRP.P) inferInstance inferInstance).unique
      ⟨hμ, hμP⟩ ⟨inferInstance, inferInstance⟩
  subst heq
  refine ⟨ρ, C, hρ, hρ1, hC.le, fun s n => ?_⟩
  have hx : StochasticVec (Pi.single s 1 : S → ℝ) :=
    ⟨fun s' => by
      rw [Pi.single_apply]
      split_ifs <;> norm_num, by simp⟩
  have h := hmix (Pi.single s 1) n
  simpa [single_one_vecMul] using h


-- created on 2026-09-26