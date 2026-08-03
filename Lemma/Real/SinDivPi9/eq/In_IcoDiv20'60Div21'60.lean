import sympy.core.relational
import Lemma.Nat.Ge.of.Gt
import Lemma.Set.In_Ico.is.Le.Lt
import Lemma.Set.In_IooDivS.of.In_Ico0.Sub.eq.DivSqrt3'2
import Lemma.Real.SinMul3.eq.SubMul3_Mul4SinMul3
import Lemma.Real.SinDivPi3.eq.DivSqrt3'2
import Lemma.Real.SinDivPi9.gt.Zero
import Lemma.Real.SinDivPi9.lt.Div1'2
open Set Real Nat


@[main]
private lemma main:
-- imply
  (π / 9).sin ∈ Ioo (20 / 60) (21 / 60) := by
-- proof
  denote h_t : t = π / 9
  rw [← h_t]
  norm_num
  have h_3t : 3 * t = π / 3 := by
     rw [h_t]
     ring
  have h_f : f (sin t) = sin (3 * t) := by
    unfold f
    rw [SinMul3.eq.SubMul3_Mul4SinMul3]
  rw [h_3t] at h_f
  rw [SinDivPi3.eq.DivSqrt3'2] at h_f
  have h_pos := SinDivPi9.gt.Zero
  rw [← h_t] at h_pos
  have h_Ge_0 := Ge.of.Gt h_pos
  have h_Lt := SinDivPi9.lt.Div1'2
  unfold f at h_f
  have := In_Ico.of.Le.Lt h_Ge_0 h_Lt
  have := In_IooDivS.of.In_Ico0.Sub.eq.DivSqrt3'2 this h_f
  simp at this
  norm_num at this
  assumption


-- created on 2025-03-24
