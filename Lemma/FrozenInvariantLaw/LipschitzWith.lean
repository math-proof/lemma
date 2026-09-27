import Mathlib.Topology.EMetricSpace.Lipschitz
import sympy.stats.frozen_invariant_law
import sympy.Basic
import Lemma.Real.Norm.le.Sum_Abs
import Lemma.FrozenInvariantLaw.Sum_AbsSub.le.MulDivMulCMixLQHQDist


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {d : ℕ}
  {r : ℝ}
  {Q : EuclideanVec d → Matrix S S ℝ}
  {hMix : UniformExponentialMixing r Q}
-- given
  (w : FrozenInvariantLawWitness r Q hMix) :
-- imply
  LipschitzWith (Real.toNNReal (hMix.cMix * hMix.hQ.lQ / hMix.γ)) (fun θ => w.μ (actor_box_projection r θ)) := by
-- proof
  refine LipschitzWith.of_dist_le' fun θ θ' => ?_
  rw [dist_eq_norm]
  exact (Real.Norm.le.Sum_Abs _).trans (by simpa using FrozenInvariantLaw.Sum_AbsSub.le.MulDivMulCMixLQHQDist w θ θ')


-- created on 2026-09-26
