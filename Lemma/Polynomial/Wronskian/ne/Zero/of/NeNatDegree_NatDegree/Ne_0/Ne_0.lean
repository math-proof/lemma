import Mathlib
import sympy.Basic
open Polynomial


/--
[roth_wronskian_ne_zero_of_natDegree_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  [Field K] [CharZero K]
  {f g : K[X]}
-- given
  (hdeg : f.natDegree ≠ g.natDegree)
  (hf : f ≠ 0)
  (hg : g ≠ 0) :
-- imply
  wronskian f g ≠ 0 := by
-- proof
  intro hw
  unfold wronskian at hw
  if hfdeg : f.natDegree = 0 then
    have hgdeg : g.natDegree ≠ 0 := by aesop
    have hfd : f.derivative = 0 := derivative_eq_zero.mpr hfdeg
    rw [hfd, zero_mul, sub_zero] at hw
    apply mul_ne_zero hf (derivative_ne_zero.mpr hgdeg) hw
  else if hgdeg : g.natDegree = 0 then
    have hgd : g.derivative = 0 := derivative_eq_zero.mpr hgdeg
    rw [hgd, mul_zero, zero_sub] at hw
    apply neg_ne_zero.mpr (mul_ne_zero (derivative_ne_zero.mpr hfdeg) hg) hw
  else
    have hfd : f.derivative ≠ 0 := derivative_ne_zero.mpr hfdeg
    have hgd : g.derivative ≠ 0 := derivative_ne_zero.mpr hgdeg
    have hdegrees : (f * g.derivative).degree = (f.derivative * g).degree := by
      rw [degree_eq_natDegree (mul_ne_zero hf hgd),
        degree_eq_natDegree (mul_ne_zero hfd hg),
        natDegree_mul hf hgd, natDegree_mul hfd hg,
        natDegree_derivative, natDegree_derivative]
      norm_cast
      omega
    have hlc : (f * g.derivative).leadingCoeff ≠
        (f.derivative * g).leadingCoeff := by
      simp only [leadingCoeff_mul, leadingCoeff_derivative]
      intro heq
      have hflc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf
      have hglc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg
      apply hdeg
      apply Nat.cast_injective (R := K)
      apply (mul_left_cancel₀ (mul_ne_zero hflc hglc))
      ·
        apply Eq.symm
        simpa [mul_assoc, mul_left_comm, mul_comm] using heq
    have hlead := leadingCoeff_sub_of_degree_eq hdegrees hlc
    rw [hw, leadingCoeff_zero] at hlead
    apply sub_ne_zero.mpr hlc hlead.symm


-- created on 2026-10-21
