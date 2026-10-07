import Lemma.Complex.Arg.in.IocNegPiPi
import Lemma.Set.Add.in.Ioc.of.In.In
open Complex
@[main]
private lemma main
  {A B : ℂ}
-- given
  (h : arg A + arg B > π) :
-- imply
  ⌈(arg A + arg B) / (π * 2) - 1 / 2⌉ = 1 := by
-- proof
  have hA : arg A ∈ Ioc (-π) π := Arg.in.IocNegPiPi A
  have hB : arg B ∈ Ioc (-π) π := Arg.in.IocNegPiPi B
  have hAlo : -π < arg A := (Set.mem_Ioc.mp hA).1
  have hAhi : arg A ≤ π := (Set.mem_Ioc.mp hA).2
  have hBlo : -π < arg B := (Set.mem_Ioc.mp hB).1
  have hBhi : arg B ≤ π := (Set.mem_Ioc.mp hB).2
  have hpi_pos : (0 : ℝ) < π * 2 := by linarith [Real.pi_pos]
  set s : ℝ := arg A + arg B with hs
  have h3lo : (0 : ℝ) < s / (π * 2) - 1 / 2 := by
    have h_s_gt : s > π := by linarith
    have : s / (π * 2) > π / (π * 2) := by
      apply div_lt_div_of_pos_right h_s_gt hpi_pos
    have : π / (π * 2) = 1 / 2 := by
      field_simp
    linarith
  have h3hi : s / (π * 2) - 1 / 2 < 1 := by
    have h_s_le : s ≤ π + π := by linarith
    have : s / (π * 2) ≤ (π + π) / (π * 2) := by
      apply div_le_div_of_nonneg_right h_s_le
      linarith [Real.pi_pos]
    have : (π + π) / (π * 2) = 1 := by
      field_simp
      linarith [Real.pi_pos]
    linarith
  set c : ℝ := s / (π * 2) - 1 / 2 with hc
  have h_pos : (0 : ℤ) < ⌈c⌉ := Int.ceil_pos.mpr h3lo
  have h_lt2 : (⌈c⌉ : ℝ) < 2 := by
    have : (⌈c⌉ : ℝ) < c + 1 := Int.ceil_lt_add_one c
    linarith
  have h_ceil_lt2 : ⌈c⌉ < 2 := by exact_mod_cast h_lt2
  omega
-- created on 2018-10-27
