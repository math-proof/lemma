import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import sympy.dynamics.actor_critic
import sympy.Basic
import Lemma.Real.IsCompact_ActorBox
import Lemma.Matrix.IsCompact


@[path]
private lemma main
  {S : Type*} [Fintype S]
  {A : Type*} [Fintype A]
  {d : ℕ}
  {m : ℕ}
-- given
  (data : BoxedFiniteStateData S A d m)
  (rW : ℝ) :
-- imply
  IsCompact (absorbing_set data rW) := by
-- proof
  exact (Real.IsCompact_ActorBox d data.rTheta).prod ((isCompact_closedBall 0 rW).prod Matrix.IsCompact)


-- created on 2026-09-26
