import sympy.stats.frozen_invariant_law
import sympy.Basic
import Lemma.FrozenInvariantLaw.Nonempty_FrozenInvariantLawWitness.of.UniformExponentialMixing
import Lemma.UniformExponentialMixing.Any_EqHQAndEqCMixAndEqAndAll_EqToFunSemigroupVecMul_Exp.of.ShortNoteGeneratorAssumptions.MatrixExponentialMixingBound.Gt_0.Ge_1


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {d : ℕ}
  {r : ℝ}
  {Q : EuclideanVec d → Matrix S S ℝ}
  {cMix γ : ℝ}
-- given
  (h₀ : 1 ≤ cMix)
  (h₁ : 0 < γ)
  (h₂ : MatrixExponentialMixingBound r Q cMix γ)
  (hQ : ShortNoteGeneratorAssumptions r Q) :
-- imply
  ∃ μ : EuclideanVec d → S → ℝ, (∀ θ ∈ actor_box d r, InvariantLaw (μ θ) (Q θ)) ∧ (∀ θ ∈ actor_box d r, ∀ ν, InvariantLaw ν (Q θ) → ν = μ θ) ∧ ∀ θ ∈ actor_box d r, ∀ θ' ∈ actor_box d r, ∑ i, |μ θ i - μ θ' i| ≤ cMix * hQ.lQ / γ * dist θ θ' := by
-- proof
  obtain ⟨hMix, hq, hc, hγ, -⟩ := UniformExponentialMixing.Any_EqHQAndEqCMixAndEqAndAll_EqToFunSemigroupVecMul_Exp.of.ShortNoteGeneratorAssumptions.MatrixExponentialMixingBound.Gt_0.Ge_1 h₀ h₁ h₂ hQ
  obtain ⟨w⟩ := FrozenInvariantLaw.Nonempty_FrozenInvariantLawWitness.of.UniformExponentialMixing hMix
  refine ⟨w.μ, w.invariant, w.unique, fun θ h θ' h' => ?_⟩
  have := w.lipschitz θ h θ' h'
  rwa [hq, hc, hγ] at this


-- created on 2026-09-26
