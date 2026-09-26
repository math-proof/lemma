import sympy.stats.frozen_invariant_law
import sympy.Basic
import Lemma.ActorBox.ActorBoxProjection.in.ActorBox.of.Ge_0
import Lemma.ActorBox.Dist.le.Dist.of.EuclideanVec


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {d : ℕ}
  {r : ℝ}
  {Q : EuclideanVec d → Matrix S S ℝ}
  {hMix : UniformExponentialMixing r Q}
-- given
  (w : FrozenInvariantLawWitness r Q hMix)
  (θ θ' : EuclideanVec d) :
-- imply
  ∑ i, |w.μ (actor_box_projection r θ) i - w.μ (actor_box_projection r θ') i| ≤ hMix.cMix * hMix.hQ.lQ / hMix.γ * dist θ θ' := by
-- proof
  have hr := hMix.hQ.r_pos.le
  apply (w.lipschitz _ (ActorBox.ActorBoxProjection.in.ActorBox.of.Ge_0 hr θ) _ (ActorBox.ActorBoxProjection.in.ActorBox.of.Ge_0 hr θ')).trans (mul_le_mul_of_nonneg_left (ActorBox.Dist.le.Dist.of.EuclideanVec r θ θ') _)
  exact div_nonneg (mul_nonneg (by linarith [hMix.cMix_ge_one]) hMix.hQ.lQ_nonneg) hMix.γ_pos.le


-- created on 2026-09-26
