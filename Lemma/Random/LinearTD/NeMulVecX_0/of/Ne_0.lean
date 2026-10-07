import sympy.stats.linear_td
import sympy.Basic
open Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {d : ℕ}
  {spec : LinearTDSpec S d}
  {z : Fin d → ℝ}
-- given
  (h : z ≠ 0) :
-- imply
  spec.X *ᵥ z ≠ 0 := by
-- proof
  intro hX
  apply h
  funext i
  refine Fintype.linearIndependent_iff.1 spec.hx z ?_ i
  funext s
  simpa [mulVec, dotProduct, LinearTDSpec.X, mul_comm] using congrFun hX s


-- created on 2026-09-26
