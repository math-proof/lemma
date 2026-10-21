import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma exists_padicInt_coe_eq_pow_mul
  (q : ℕ) [Fact q.Prime]
  (a : ℚ_[q]) :
  -- imply
  ∃ (k : ℕ) (z : ℤ_[q]), (z : ℚ_[q]) = (q : ℚ_[q]) ^ k * a := by
  -- proof
  if ha : a = 0 then
    refine ⟨0, 0, by simp [ha]⟩
  else
    have hq1 : (1 : ℝ) ≤ q := by
      exact_mod_cast (Fact.out : q.Prime).one_lt.le
    have hq0 : (q : ℝ) ≠ 0 := by
      positivity
    refine ⟨(-a.valuation).toNat, Subtype.mk ((q : ℚ_[q]) ^ (-a.valuation).toNat * a) ?_, rfl⟩
    rw [norm_mul, Padic.norm_p_pow, Padic.norm_eq_zpow_neg_valuation ha, ← zpow_add₀ hq0]
    refine zpow_le_one_of_nonpos₀ hq1 ?_
    have := Int.self_le_toNat (-a.valuation)
    omega

private lemma coe_tmul
  (q : ℕ) [Fact q.Prime]
  (T : Type) [AddCommGroup T] [Module ℤ_[q] T]
  (z : ℤ_[q])
  (t : T) :
  -- imply
  TensorProduct.tmul ℤ_[q] (z : ℚ_[q]) t = TensorProduct.tmul ℤ_[q] (1 : ℚ_[q]) (z • t) := by
  -- proof
  rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  rfl

/--
[TensorProduct_exists_pow_smul_eq_one_tmul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_TensorProduct_exists_pow_smul_eq_one_tmul.lean)
-/
@[path]
private lemma main
  (q : ℕ) [Fact q.Prime]
  (T : Type) [AddCommGroup T] [Module ℤ_[q] T]
  (w : TensorProduct ℤ_[q] ℚ_[q] T) :
  -- imply
  ∃ (k : ℕ) (t : T), ((q : ℚ_[q]) ^ k) • w = TensorProduct.tmul ℤ_[q] (1 : ℚ_[q]) t := by
  -- proof
  induction w using TensorProduct.inductionOn with
  | tmul a t =>
    obtain ⟨k, z, hz⟩ := exists_padicInt_coe_eq_pow_mul q a
    refine ⟨k, z • t, ?_⟩
    rw [TensorProduct.smul_tmul', smul_eq_mul, ← hz, coe_tmul]
  | add x y hx hy =>
    obtain ⟨k, t, ht⟩ := hx
    obtain ⟨l, s, hs⟩ := hy
    refine ⟨k + l, ((q : ℤ_[q]) ^ l) • t + ((q : ℤ_[q]) ^ k) • s, ?_⟩
    rw [smul_add, pow_add, mul_comm ((q : ℚ_[q]) ^ k), mul_smul, ht, mul_comm, mul_smul, hs,
      TensorProduct.tmul_add, ← coe_tmul, ← coe_tmul, TensorProduct.smul_tmul',
      TensorProduct.smul_tmul', smul_eq_mul, mul_one, smul_eq_mul, mul_one]
    push_cast
    rfl


-- created on 2026-10-20
