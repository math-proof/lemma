import Mathlib
import sympy.Basic
import sympy.atlas.Algebra.Polynomial.RootBound
open Polynomial


namespace Polynomial

/--
[aeval_lt_l1Norm_of_monic_of_aeval_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/RootBound.lean)
-/
@[path]
lemma aeval_lt_l1Norm_of_monic_of_aeval_eq_zero
  [Field K] [Field L] [Algebra K L]
  {v : AbsoluteValue K ℝ}
  {w : AbsoluteValue L ℝ} [AbsoluteValue.LiesOver w v]
  {f : Polynomial K}
  {α : L}
-- given
  (hf : f.Monic)
  (hroot : aeval α f = 0) :
-- imply
  w α < l1Norm v f := by
-- proof
  have hcompat : ∀ x : K, w (algebraMap K L x) = v x := fun x =>
    DFunLike.congr_fun (AbsoluteValue.LiesOver.comp_eq w v) x
  obtain hsmall | hbig := lt_or_ge (w α) 1
  · exact hsmall.trans_le (one_le_l1Norm_of_monic v f hf)
  · have hroot2 : eval₂ (algebraMap K L) α f = 0 := by
    rwa [← aeval_def]
    rw [eval₂_eq_sum_range, Finset.sum_range_succ] at hroot2
    have hlead : algebraMap K L (f.coeff f.natDegree) * α ^ f.natDegree
      = α ^ f.natDegree := by
      rw [hf.coeff_natDegree, map_one, one_mul]
    rw [hlead] at hroot2
    have hpow : α ^ f.natDegree
      = -∑ i ∈ Finset.range f.natDegree,
        algebraMap K L (f.coeff i) * α ^ i :=
      eq_neg_of_add_eq_zero_right hroot2
    have htriangle : w α ^ f.natDegree
      ≤ ∑ i ∈ Finset.range f.natDegree, v (f.coeff i) * w α ^ i := by
      calc w α ^ f.natDegree = w (α ^ f.natDegree) :=
        (AbsoluteValue.map_pow w α f.natDegree).symm
        _ = w (∑ i ∈ Finset.range f.natDegree,
          algebraMap K L (f.coeff i) * α ^ i) := by
          rw [hpow, AbsoluteValue.map_neg]
        _ ≤ ∑ i ∈ Finset.range f.natDegree,
          w (algebraMap K L (f.coeff i) * α ^ i) :=
          AbsoluteValue.sum_le w _ _
        _ = ∑ i ∈ Finset.range f.natDegree, v (f.coeff i) * w α ^ i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [AbsoluteValue.map_mul w _ _, AbsoluteValue.map_pow w _ _,
            hcompat]
    have hsum : ∑ i ∈ Finset.range f.natDegree, v (f.coeff i) * w α ^ i
      ≤ (∑ i ∈ Finset.range f.natDegree, v (f.coeff i))
        * w α ^ (f.natDegree - 1) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (v.nonneg _)
      apply pow_le_pow_right₀ hbig
      have := Finset.mem_range.mp hi
      omega
    have hmain : w α ^ f.natDegree
      ≤ (∑ i ∈ Finset.range f.natDegree, v (f.coeff i))
        * w α ^ (f.natDegree - 1) :=
      htriangle.trans hsum
    obtain hzero | hpos := Nat.eq_zero_or_pos f.natDegree
    · rw [hzero] at hmain
      simp at hmain
      linarith
    · have hposW : 0 < w α := lt_of_lt_of_le zero_lt_one hbig
      have hpow_pos : 0 < w α ^ (f.natDegree - 1) := pow_pos hposW _
      have hsplit : w α ^ f.natDegree
        = w α ^ (f.natDegree - 1) * w α := by
        conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ f.natDegree from hpos),
          pow_succ]
      have hle_S : w α ≤ ∑ i ∈ Finset.range f.natDegree, v (f.coeff i) :=
        le_of_mul_le_mul_left (by
          rw [← hsplit, mul_comm (w α ^ (f.natDegree - 1))]
          exact hmain) hpow_pos
      have hL1 := l1Norm_eq_sum_range_add_one_of_monic v f hf
      rw [hL1]
      linarith

end Polynomial


-- created on 2026-10-20
-- updated on 2026-10-23
