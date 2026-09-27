import sympy.stats.markov_reward_process
import sympy.Basic
import sympy.matrices.dense
import Lemma.FiniteMRP.PosDefD
import Lemma.FiniteMRP.DotVecMul_MulDP.le.DotVecMul_D
open Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {MRP : FiniteMRP S} :
-- imply
  NegDefAsymm MRP.K := by
-- proof
  refine ⟨⟨fun z hz => ?_⟩⟩
  have hpos := PosDef.dotProduct_mulVec_pos (FiniteMRP.PosDefD (MRP := MRP)) hz
  rw [star_trivial, dotProduct_mulVec] at hpos
  have hle := FiniteMRP.DotVecMul_MulDP.le.DotVecMul_D (MRP := MRP) z
  have hK : z ⬝ᵥ (-MRP.K) *ᵥ z = z ᵥ* MRP.D ⬝ᵥ z - MRP.γ * (z ᵥ* (MRP.D * MRP.P) ⬝ᵥ z) := by
    rw [dotProduct_mulVec, FiniteMRP.K, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, neg_sub,
      vecMul_sub, vecMul_smul, sub_dotProduct, smul_dotProduct, smul_eq_mul]
  rw [hK]
  nlinarith [MRP.hγ.1, MRP.hγ.2]


-- created on 2026-09-26