import sympy.stats.linear_td
import sympy.Basic
import sympy.matrices.dense
import Lemma.FiniteMRP.NegDefAsymmK
import Lemma.LinearTDSpec.NeMulVecX_0.of.Ne_0
open Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {d : ℕ}
  {spec : LinearTDSpec S d} :
-- imply
  NegDefAsymm spec.A := by
-- proof
  refine ⟨⟨fun z hz => ?_⟩⟩
  have hK := (FiniteMRP.NegDefAsymmK (MRP := spec.toFiniteMRP)).nd.pd _ (LinearTDSpec.NeMulVecX_0.of.Ne_0 (spec := spec) hz)
  rw [neg_mulVec, dotProduct_neg] at hK
  rwa [show spec.A = Matrix.transpose spec.X * spec.K * spec.X by simp only [LinearTDSpec.A, FiniteMRP.K, Matrix.mul_assoc], neg_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_neg,
    dotProduct_mulVec, vecMul_transpose]


-- created on 2026-09-26
