import Lemma.Complex.Arg.in.IocNegPiPi
import Lemma.Int.LeAbs.is.LeNeg.Le
import Lemma.Int.LeCeil.is.Le
import Lemma.Nat.LeMulS.of.Gt_0.Le
import Lemma.Nat.Lt0Mul.of.Gt_0.Gt_0
import Lemma.Nat.LtMulS.of.Gt_0.Lt
import Lemma.Real.GtPi0
import Lemma.Set.InDiv.of.In_Ioc.Gt_0
import Lemma.Set.In_Ioc.is.Lt.Le
open Complex Int Nat Real Set


@[main]
private lemma main
-- given
  (z : ℂ) :
-- imply
  |⌈3 * arg z / (2 * π) - 1 / 2⌉| ≤ 1 := by
-- proof
  have h2π := Lt0Mul.of.Gt_0.Gt_0 (by norm_num : (2 : ℝ) > 0) GtPi0
  have hmem := InDiv.of.In_Ioc.Gt_0 (Arg.in.IocNegPiPi z) h2π
  rw [(by field_simp : π / (2 * π) = (1 / 2 : ℝ)),
    (by field_simp : (-π) / (2 * π) = (-1 / 2 : ℝ))] at hmem
  obtain ⟨hlt, hle⟩ := Lt.Le.of.In_Ioc hmem
  have hdiv : 3 * arg z / (2 * π) = 3 * (arg z / (2 * π)) := by
    ring
  apply LeAbs.of.LeNeg.Le
  ·
    have hx_gt : (↑(-2 : ℤ) : ℝ) < 3 * arg z / (2 * π) - 1 / 2 := by
      have := LtMulS.of.Gt_0.Lt (by norm_num : (3 : ℝ) > 0) hlt
      rw [hdiv]
      linarith
    have : (-2 : ℤ) < ⌈3 * arg z / (2 * π) - 1 / 2⌉ :=
      (Int.lt_ceil (z := -2)).mpr hx_gt
    omega
  ·
    apply LeCeil.of.Le
    have := LeMulS.of.Gt_0.Le (by norm_num : (3 : ℝ) > 0) hle
    rw [hdiv]
    linarith


-- created on 2026-08-28
