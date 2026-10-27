import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.ModularCurve.LaurentCoeff
open ModularCurve


/--
[ModularCurve_linearIndependent_coeffMap_algebraMap](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_linearIndependent_coeffMap_algebraMap.lean)
-/
@[path]
private lemma main
  [Field K] [Field L] [Algebra K L]
  {v : ι → LaurentSeries K}
-- given
  (hv : LinearIndependent K v) :
-- imply
  LinearIndependent L (fun i => coeffMap (algebraMap K L) (v i)) := by
-- proof
  classical
    rw [linearIndependent_iff'] at hv ⊢
    intro s g hg i hi
    let B := Module.Free.chooseBasis K L
    have key : ∀ j, ∑ i ∈ s, (B.repr (g i) j) • v i = 0 := by
      intro j
      ext n
      have hn : (∑ i ∈ s, g i • coeffMap (algebraMap K L) (v i)).coeff n = 0 := by
        rw [hg]; rfl
      rw [HahnSeries.coeff_sum] at hn ⊢
      simp_rw [HahnSeries.coeff_smul, coeffMap_coeff, smul_eq_mul] at hn ⊢
      have h2 := congrArg (fun x : L => B.repr x j) hn
      simp only [map_sum, map_zero, Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_finsetSum, Finset.sum_apply] at h2
      rw [show (0 : LaurentSeries K).coeff n = 0 from rfl, ← h2]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm (g i) _, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
    have hcoord : ∀ j, B.repr (g i) j = 0 := fun j => hv s (fun i => B.repr (g i) j) (key j) i hi
    have : B.repr (g i) = 0 := Finsupp.ext fun j => hcoord j
    exact B.repr.map_eq_zero_iff.mp this


-- created on 2026-10-23
