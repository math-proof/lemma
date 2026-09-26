import sympy.stats.markov_reward_process
import sympy.Basic
import Mathlib.Analysis.Convex.Mul
open Matrix Finset


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {MRP : FiniteMRP S}
-- given
  (v : S → ℝ) :
-- imply
  ∑ s, MRP.μ s * (MRP.P *ᵥ v) s ^ 2 ≤ ∑ s, MRP.μ s * v s ^ 2 := by
-- proof
  have hP : RowStochastic MRP.P := inferInstance
  have hμ : StochasticVec MRP.μ := inferInstance
  have hjensen : ∀ s, (MRP.P *ᵥ v) s ^ 2 ≤ ∑ j, MRP.P s j * v j ^ 2 := by
    intro s
    have h := (Even.convexOn_pow (𝕜 := ℝ) (even_two)).map_sum_le (t := univ) (w := MRP.P s) (p := v)
      (fun j _ => (hP.stochastic s).nonneg j) (hP.stochastic s).rowsum (fun j _ => Set.mem_univ _)
    simpa [mulVec, dotProduct] using h
  calc ∑ s, MRP.μ s * (MRP.P *ᵥ v) s ^ 2
      ≤ ∑ s, MRP.μ s * ∑ j, MRP.P s j * v j ^ 2 :=
        sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hjensen s) (hμ.nonneg s)
    _ = ∑ j, (∑ s, MRP.μ s * MRP.P s j) * v j ^ 2 := by
        simp only [mul_sum, sum_mul]
        rw [sum_comm]
        simp only [mul_assoc]
    _ = ∑ j, MRP.μ j * v j ^ 2 := by
        have h := (inferInstance : Stationary MRP.μ MRP.P).stationary
        refine sum_congr rfl fun j _ => ?_
        have hj := congrFun h j
        simp only [vecMul, dotProduct] at hj
        rw [hj]


-- created on 2026-09-26