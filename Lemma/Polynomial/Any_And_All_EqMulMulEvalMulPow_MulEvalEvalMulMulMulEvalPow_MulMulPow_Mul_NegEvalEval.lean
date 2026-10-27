import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma eval_inv_eq_eval_reverse_mul_pow
  (f : Polynomial ℂ)
  (Y : ℂ)
  -- given
  (hY : Y ≠ 0) :
  -- imply
  f.eval Y⁻¹ = f.reverse.eval Y * Y ^ (-(f.natDegree : ℤ)) := by
  -- proof
  let _ : Invertible Y⁻¹ := invertibleOfNonzero (inv_ne_zero hY)
  have h := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) Y⁻¹ f
  simp only [Polynomial.eval₂_id] at h
  rw [invOf_eq_inv, inv_inv] at h
  rw [← h, zpow_neg, zpow_natCast, inv_pow]

/--
[Polynomial_exists_eval_mul_cpow_mul_eval_eq_of_ne_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Polynomial_exists_eval_mul_cpow_mul_eval_eq_of_ne_zero.lean)
-/
@[path]
private lemma main
  (q : ℂ)
  (P Pd Q Qd : Polynomial ℂ)
  (m md : ℤ)
  -- given
  (hq : q ≠ 0)
  (hP : P ≠ 0)
  (hQd : Qd ≠ 0) :
  -- imply
  ∃ (R₁ R₂ : Polynomial ℂ) (r : ℤ), R₂ ≠ 0 ∧ ∀ s : ℂ, R₂.eval (q ^ s) * (q ^ ((md : ℂ) * s) * Pd.eval (q ^ (-s))) * Q.eval (q ^ s) = (R₁.eval (q ^ s) * q ^ ((r : ℂ) * s)) * (q ^ ((m : ℂ) * (-s)) * P.eval (q ^ s)) * Qd.eval (q ^ (-s)) := by
  -- proof
  refine ⟨Q * Pd.reverse, P * Qd.reverse, md + m + (Qd.natDegree : ℤ) - (Pd.natDegree : ℤ),
    mul_ne_zero hP (by rwa [Ne, Polynomial.reverse_eq_zero]), fun s => ?_⟩
  set Y : ℂ := q ^ s with hY
  have hY0 : Y ≠ 0 := by
    rw [hY]
    intro h
    apply hq ((Complex.cpow_eq_zero_iff q s).mp h).1
  have hX : q ^ (-s) = Y⁻¹ := by
    rw [hY, Complex.cpow_neg]
  have h1 : q ^ ((md : ℂ) * s) = Y ^ md := by
    rw [hY, Complex.cpow_int_mul]
  have h2 : q ^ ((m : ℂ) * (-s)) = Y ^ (-m) := by
    rw [hY, ← Complex.cpow_int_mul, Int.cast_neg]
    ring_nf
  have h3 : q ^ (((md + m + (Qd.natDegree : ℤ) - (Pd.natDegree : ℤ) : ℤ) : ℂ) * s) =
      Y ^ (md + m + (Qd.natDegree : ℤ) - (Pd.natDegree : ℤ)) := by
    rw [hY, Complex.cpow_int_mul]
  rw [hX, h1, h2, h3, Polynomial.eval_mul, Polynomial.eval_mul,
    eval_inv_eq_eval_reverse_mul_pow Pd Y hY0, eval_inv_eq_eval_reverse_mul_pow Qd Y hY0]
  have hz : Y ^ md * Y ^ (-(Pd.natDegree : ℤ)) =
      Y ^ (md + m + (Qd.natDegree : ℤ) - (Pd.natDegree : ℤ)) * Y ^ (-m) * Y ^ (-(Qd.natDegree : ℤ)) := by
    rw [← zpow_add₀ hY0, ← zpow_add₀ hY0, ← zpow_add₀ hY0]
    congr 1
    ring
  calc
    _ = (P.eval Y * Qd.reverse.eval Y * Pd.reverse.eval Y * Q.eval Y) * (Y ^ md * Y ^ (-(Pd.natDegree : ℤ))) := by
      ring
    _ = (P.eval Y * Qd.reverse.eval Y * Pd.reverse.eval Y * Q.eval Y) * (Y ^ (md + m + (Qd.natDegree : ℤ) - (Pd.natDegree : ℤ)) * Y ^ (-m) * Y ^ (-(Qd.natDegree : ℤ))) := by
      rw [hz]
    _ = (Q.eval Y * Pd.reverse.eval Y) * Y ^ (md + m + (Qd.natDegree : ℤ) - (Pd.natDegree : ℤ)) * (Y ^ (-m) * P.eval Y) * (Qd.reverse.eval Y * Y ^ (-(Qd.natDegree : ℤ))) := by
      ring


-- created on 2026-10-20
