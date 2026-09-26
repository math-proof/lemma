import sympy.stats.frozen_invariant_law
import sympy.Basic
import Lemma.UniformExponentialMixing.Sum_AbsResolvent.le.MulDivCMixSum_Abs.of.EqSum_0.In_ActorBox
import Lemma.UniformExponentialMixing.EqResolventVecMul.of.EqSum_0.In_ActorBox


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {d : ℕ}
  {r : ℝ}
  {Q : EuclideanVec d → Matrix S S ℝ}
-- given
  (hMix : UniformExponentialMixing r Q) :
-- imply
  Nonempty (FrozenResolventWitness r Q hMix) := by
-- proof
  exact ⟨⟨hMix.resolvent, fun _ h₀ _ h₁ => UniformExponentialMixing.Sum_AbsResolvent.le.MulDivCMixSum_Abs.of.EqSum_0.In_ActorBox h₀ h₁ hMix, fun _ h₀ _ h₁ => UniformExponentialMixing.EqResolventVecMul.of.EqSum_0.In_ActorBox h₀ h₁ hMix⟩⟩


-- created on 2026-09-26
