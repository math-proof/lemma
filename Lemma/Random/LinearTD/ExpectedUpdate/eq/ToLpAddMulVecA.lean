import sympy.stats.linear_td
import sympy.Basic
open Finset Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {d : ℕ}
  {spec : LinearTDSpec S d}
-- given
  (w : EuclideanVec d) :
-- imply
  spec.expected_update w = WithLp.toLp 2 (spec.A *ᵥ WithLp.ofLp w + spec.b) := by
-- proof
  have hP : RowStochastic spec.P := inferInstance
  have hc : ∀ s, (spec.X *ᵥ WithLp.ofLp w) s = inner ℝ (spec.x s) w := fun s => by
    simp [mulVec, dotProduct, LinearTDSpec.X, PiLp.inner_apply, mul_comm]
  have hR : spec.A *ᵥ WithLp.ofLp w + spec.b = Matrix.transpose spec.X *ᵥ (spec.D *ᵥ ((spec.γ • spec.P - 1) *ᵥ (spec.X *ᵥ WithLp.ofLp w) + spec.r)) := by
    simp only [LinearTDSpec.A, LinearTDSpec.b, ← mulVec_mulVec, mulVec_add]
  rw [hR]
  ext i
  simp only [LinearTDSpec.expected_update, LinearTDSpec.update, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, mulVec_transpose, vecMul, dotProduct,
    FiniteMRP.D, mulVec_diagonal, sub_mulVec, smul_mulVec, one_mulVec, Pi.add_apply, Pi.sub_apply, ← hc]
  refine sum_congr rfl fun s _ => ?_
  rw [show (spec.x s).ofLp i = spec.X s i from rfl]
  calc _ = spec.μ s * spec.X s i * (spec.r s * ∑ x, spec.P s x + spec.γ * ∑ x, spec.P s x * (spec.X *ᵥ WithLp.ofLp w) x - (spec.X *ᵥ WithLp.ofLp w) s * ∑ x, spec.P s x) := by
        simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
        exact sum_congr rfl fun x _ => by ring
    _ = _ := by
      rw [(hP.stochastic s).rowsum, show (spec.P *ᵥ (spec.X *ᵥ WithLp.ofLp w)) s = ∑ x, spec.P s x * (spec.X *ᵥ WithLp.ofLp w) x from rfl]
      ring


-- created on 2026-09-26
