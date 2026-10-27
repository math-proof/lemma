import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.ModularCurve.LaurentCoeff
open ModularCurve


/--
[ModularCurve_linearIndependent_coeffEmb_of_linearIndependent](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_linearIndependent_coeffEmb_of_linearIndependent.lean)
-/
@[path]
private lemma main
  {L : Type u} [Field L] [CharZero L]
  {ι : Type v}
  {v : ι → LaurentSeries ℚ}
-- given
  (hv : LinearIndependent ℚ v) :
-- imply
  LinearIndependent L (fun i => coeffEmb L (v i)) := by
-- proof
  classical
    rw [linearIndependent_iff'] at hv ⊢
    intro s g hg i hi
    let b := Module.Free.chooseBasis ℚ L
    have hcoeff : ∀ (k) (n : ℤ), ∑ j ∈ s, b.repr (g j) k * (v j).coeff n = 0 := by
      intro k n
      have h := congrArg (fun x : LaurentSeries L => b.repr (x.coeff n) k) hg
      simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, smul_eq_mul, coeffEmb_coeff, HahnSeries.coeff_zero,
        map_zero, Finsupp.zero_apply, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply] at h
      rw [← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm (g j), ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
    have hrepr : ∀ k, b.repr (g i) k = 0 := by
      intro k
      refine hv s (fun j => b.repr (g j) k) ?_ i hi
      ext n
      rw [HahnSeries.coeff_sum, HahnSeries.coeff_zero]
      simp only [HahnSeries.coeff_smul, smul_eq_mul]
      exact hcoeff k n
    refine b.repr.map_eq_zero_iff.mp (Finsupp.ext fun k => hrepr k)


-- created on 2026-10-23
