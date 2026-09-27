import sympy.stats.linear_td
import sympy.stats.lyapunov
import sympy.Basic
import Lemma.LpSpace.LyapunovCandidateHalfSq.of.Ge_2
import Lemma.LinearTDSpec.DecreaseAlongHalfSq
open LpSpace


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {d : ℕ}
  {spec : LinearTDSpec S d} :
-- imply
  LyapunovFunction (fun x : EuclideanVec d => half_sq (ofL2 2 x)) (fun x => (half_sq' (ofL2 2 x)).toL2) spec.expected_update_target :=
-- proof
  ⟨LpSpace.LyapunovCandidateHalfSq.of.Ge_2 le_rfl, LinearTDSpec.DecreaseAlongHalfSq⟩


-- created on 2026-09-26
