import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.AlgebraicCurve.DivisorPushPull
import Lemma.Int.P2MUtil

open AlgebraicCurve

/--
[AlgebraicCurve_sumRamificationInertia_of_fundamentalIdentity](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_sumRamificationInertia_of_fundamentalIdentity.lean)
-/
@[path]
private lemma main
  {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F'] [FundamentalIdentity K F F']
-- given
  (hdeg : ∀ v : Place K F, v.deg ≠ 0) :
-- imply
  SumRamificationInertia K F F' := by
  refine ⟨fun v => ?_⟩
  have key := FundamentalIdentity.sum_ramificationIndex_mul_deg (K := K) (F := F) (F' := F') v
  have hsum : ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) * (w.deg : ℤ) = (v.deg : ℤ) * ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) := by
-- proof
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [← Place.deg_restrict_mul_inertiaDeg (F := F) w, Place.mem_fiber.mp hw]
    push_cast
    ring
  have hv : (v.deg : ℤ) ≠ 0 := by exact_mod_cast hdeg v
  refine mul_left_cancel₀ hv
  rw [← hsum, key, mul_comm]


-- created on 2026-10-23
