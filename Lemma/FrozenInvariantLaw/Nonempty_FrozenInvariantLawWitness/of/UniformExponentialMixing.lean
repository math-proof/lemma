import sympy.stats.frozen_invariant_law
import sympy.Basic
import Lemma.UniformExponentialMixing.InvariantLaw.Unique.of.UniformExponentialMixing.In_ActorBox
import Lemma.UniformExponentialMixing.Nonempty_FrozenResolventWitness.of.UniformExponentialMixing
import Lemma.FrozenInvariantLaw.Sum_AbsSub.le.MulDivMulCMixLQHQDist.of.FrozenResolventWitness.InvariantLaw.InvariantLaw.In_ActorBox.In_ActorBox


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {d : ℕ}
  {r : ℝ}
  {Q : EuclideanVec d → Matrix S S ℝ}
-- given
  (hMix : UniformExponentialMixing r Q) :
-- imply
  Nonempty (FrozenInvariantLawWitness r Q hMix) := by
-- proof
  classical
  obtain ⟨hR⟩ := UniformExponentialMixing.Nonempty_FrozenResolventWitness.of.UniformExponentialMixing hMix
  let μ : EuclideanVec d → S → ℝ := fun θ => if h : θ ∈ actor_box d r then (UniformExponentialMixing.InvariantLaw.Unique.of.UniformExponentialMixing.In_ActorBox h hMix).choose else 0
  have hinv : ∀ θ ∈ actor_box d r, InvariantLaw (μ θ) (Q θ) := fun θ h => by simpa [μ, h] using (UniformExponentialMixing.InvariantLaw.Unique.of.UniformExponentialMixing.In_ActorBox h hMix).choose_spec.1
  exact ⟨⟨μ, hinv, fun θ h ν hν => (UniformExponentialMixing.InvariantLaw.Unique.of.UniformExponentialMixing.In_ActorBox h hMix).unique hν (hinv θ h), fun θ h θ' h' => FrozenInvariantLaw.Sum_AbsSub.le.MulDivMulCMixLQHQDist.of.FrozenResolventWitness.InvariantLaw.InvariantLaw.In_ActorBox.In_ActorBox h h' (hinv θ h) (hinv θ' h') hR⟩⟩


-- created on 2026-09-26
