import sympy.stats.lyapunov
import Lemma.LpSpace.HalfSq.le.AddAddHalfSqInner_MulSub1HalfSqSub.of.Ge_2
import Lemma.LpSpace.Norm.le.NormToL2.of.Ge_2
import Lemma.LpSpace.Any_And_Ge_0_All_LeNormToL2_MulNorm.of.Ge_2
import Lemma.LpSpace.InnerToL2HalfSq'_ToL2.eq.SquareNorm.of.Ge_1
import Lemma.LpSpace.SumMulAbsHalfSq'_Abs.le.MulNormS.of.Ge_2
open Finset LpSpace


@[main]
private lemma main
  {p d : ℕ}
-- given
  (h : 2 ≤ p) :
-- imply
  LyapunovCandidate (fun x : EuclideanVec d => half_sq (ofL2 p x)) (fun x => (half_sq' (ofL2 p x)).toL2) := by
-- proof
  have : Fact (1 ≤ (p : ENNReal)) := ⟨by exact_mod_cast (by omega : 1 ≤ p)⟩
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast h
  have hs : ∀ z : LpSpace p d, √(half_sq z) = (√2)⁻¹ * ‖z‖ := fun z => by
    rw [half_sq, Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _), one_div, Real.sqrt_inv]
  have h2 : (√2)⁻¹ * (√2)⁻¹ = (1 / 2 : ℝ) := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num), one_div]
  refine ⟨fun x => by unfold half_sq; positivity, fun z => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : ofL2 p z = 0 ↔ z = 0 := ⟨fun h₀ => by rw [← toL2_ofL2 (p := p) z, h₀]; ext i; simp [toL2], fun h₀ => by rw [h₀]; ext i; simp [ofL2]⟩
    simp [half_sq, e]
  · refine ⟨p - 1, by linarith, fun x y => ?_⟩
    have hs' := HalfSq.le.AddAddHalfSqInner_MulSub1HalfSqSub.of.Ge_2 (x := ofL2 p x) (y := ofL2 p y) h
    have ht : (ofL2 p y - ofL2 p x).toL2 = y - x := by
      ext i
      simp [toL2, ofL2]
    have hn := Norm.le.NormToL2.of.Ge_2 (x := ofL2 p y - ofL2 p x) h
    rw [ht] at hs' hn
    simp only [half_sq] at hs' ⊢
    have hp1 : (0 : ℝ) ≤ p - 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) hp1]
  · refine ⟨2, by norm_num, fun x => ?_⟩
    have e := InnerToL2HalfSq'_ToL2.eq.SquareNorm.of.Ge_1 (x := ofL2 p x) (by omega)
    rw [toL2_ofL2] at e
    rw [e, half_sq]
    ring
  · refine ⟨2, by norm_num, fun x y => ?_⟩
    calc
      _ = ∑ i, |half_sq' (ofL2 p x) i| * |ofL2 p y i| := rfl
      _ ≤ ‖ofL2 p x‖ * ‖ofL2 p y‖ := SumMulAbsHalfSq'_Abs.le.MulNormS.of.Ge_2 h
      _ = _ := by
        rw [hs, hs]
        linear_combination (-2 * ‖ofL2 p x‖ * ‖ofL2 p y‖) * h2
  · obtain ⟨C, hC, hC'⟩ := Any_And_Ge_0_All_LeNormToL2_MulNorm.of.Ge_2 (d := d) h
    refine ⟨√2 * C, by positivity, fun x => ?_⟩
    have e : ‖ofL2 p x‖ = √2 * √(half_sq (ofL2 p x)) := by
      rw [hs, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    calc
      _ = ‖(ofL2 p x).toL2‖ := rfl
      _ ≤ C * ‖ofL2 p x‖ := hC' _
      _ = _ := by rw [e]; ring
  · exact ⟨(√2)⁻¹, by positivity, fun x => by
      rw [hs]
      exact mul_le_mul_of_nonneg_left (Norm.le.NormToL2.of.Ge_2 h) (by positivity)⟩


-- created on 2026-09-26