import sympy.stats.linear_td
import sympy.Basic
import sympy.matrices.dense
import Lemma.LinearTDSpec.NegDefAsymmA
import Lemma.LinearTDSpec.ExpectedUpdate.eq.ToLpAddMulVecA
open Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {d : ℕ}
  {spec : LinearTDSpec S d} :
-- imply
  spec.expected_update spec.td_fixed_point = 0 := by
-- proof
  have := LinearTDSpec.NegDefAsymmA (spec := spec)
  rw [LinearTDSpec.ExpectedUpdate.eq.ToLpAddMulVecA, LinearTDSpec.td_fixed_point, WithLp.ofLp_toLp, mulVec_neg, mulVec_mulVec, mul_inv_of_invertible, one_mulVec, neg_add_cancel, WithLp.toLp_zero]


-- created on 2026-09-26
