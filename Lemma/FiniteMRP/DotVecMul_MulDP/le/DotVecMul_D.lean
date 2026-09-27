import sympy.stats.markov_reward_process
import sympy.Basic
import Lemma.FiniteMRP.Sum_Mul_SquareGetMulVecP.le.Sum_Mul_Square
open Matrix Finset


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {MRP : FiniteMRP S}
-- given
  (v : S → ℝ) :
-- imply
  v ᵥ* (MRP.D * MRP.P) ⬝ᵥ v ≤ v ᵥ* MRP.D ⬝ᵥ v := by
-- proof
  have hμ : StochasticVec MRP.μ := inferInstance
  have h := FiniteMRP.Sum_Mul_SquareGetMulVecP.le.Sum_Mul_Square (MRP := MRP) v
  have e₁ : v ᵥ* MRP.D ⬝ᵥ v = ∑ s, MRP.μ s * v s ^ 2 := by
    simp only [FiniteMRP.D, vecMul_diagonal, dotProduct]
    exact sum_congr rfl fun s _ => by ring
  have e₂ : v ᵥ* (MRP.D * MRP.P) ⬝ᵥ v = ∑ s, MRP.μ s * v s * (MRP.P *ᵥ v) s := by
    rw [← vecMul_vecMul, ← dotProduct_mulVec]
    simp only [FiniteMRP.D, vecMul_diagonal, dotProduct]
    exact sum_congr rfl fun s _ => by ring
  rw [e₁, e₂]
  have hs : ∀ s, MRP.μ s * v s * (MRP.P *ᵥ v) s ≤ (MRP.μ s * v s ^ 2 + MRP.μ s * (MRP.P *ᵥ v) s ^ 2) / 2 :=
    fun s => by nlinarith [mul_nonneg (hμ.nonneg s) (sq_nonneg (v s - (MRP.P *ᵥ v) s))]
  calc _ ≤ ∑ s, (MRP.μ s * v s ^ 2 + MRP.μ s * (MRP.P *ᵥ v) s ^ 2) / 2 := sum_le_sum fun s _ => hs s
    _ = ((∑ s, MRP.μ s * v s ^ 2) + ∑ s, MRP.μ s * (MRP.P *ᵥ v) s ^ 2) / 2 := by
      rw [← sum_div, sum_add_distrib]
    _ ≤ _ := by linarith


-- created on 2026-09-26