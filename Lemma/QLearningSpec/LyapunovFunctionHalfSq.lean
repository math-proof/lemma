import sympy.stats.q_learning
import sympy.stats.lyapunov
import sympy.Basic
import Lemma.LpSpace.LyapunovCandidateHalfSq.of.Ge_2
import Lemma.QLearningSpec.DecreaseAlongHalfSq
open LpSpace


@[main]
private lemma main
  {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
  {spec : QLearningSpec S A} :
-- imply
  LyapunovFunction (fun x : EuclideanVec (Fintype.card (S × A)) => half_sq (ofL2 spec.pmin x)) (fun x => (half_sq' (ofL2 spec.pmin x)).toL2) spec.expected_update_target :=
-- proof
  ⟨LpSpace.LyapunovCandidateHalfSq.of.Ge_2 (le_max_left _ _), QLearningSpec.DecreaseAlongHalfSq⟩


-- created on 2026-09-26
