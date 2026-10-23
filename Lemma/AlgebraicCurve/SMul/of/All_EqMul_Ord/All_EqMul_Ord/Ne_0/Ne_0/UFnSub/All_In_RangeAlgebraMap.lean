import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_DivisorClassGroup
open KaehlerDifferential
open AlgebraicCurve


/-- ported from external source -/

private lemma  D_pow_char
  {K F : Type*}
  [Field K]
  [Field F]
  [Algebra K F]
  (p : ℕ) [CharP K p] (h : F) : D K F (h ^ p) = 0 := by
  have : CharP F p := (algebraMap K F).charP_iff_charP p |>.mp inferInstance
  rw [Derivation.leibniz_pow, smul_comm, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul,
    smul_zero]

private lemma  dlog_mul
  {K F : Type*}
  [Field K]
  [Field F]
  [Algebra K F]
  {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
  (a * b)⁻¹ • D K F (a * b) = a⁻¹ • D K F a + b⁻¹ • D K F b := by
  rw [Derivation.leibniz, smul_add, smul_smul, smul_smul, mul_inv, add_comm]
  congr 1
  · rw [show a⁻¹ * b⁻¹ * b = a⁻¹ from inv_mul_cancel_right₀ hb _]
  · rw [show a⁻¹ * b⁻¹ * a = b⁻¹ by rw [mul_comm a⁻¹, inv_mul_cancel_right₀ ha]]

private lemma  dlog_algebraMap
  {K F : Type*}
  [Field K]
  [Field F]
  [Algebra K F]
  (c : K) : (algebraMap K F c)⁻¹ • D K F (algebraMap K F c) = 0 := by
  rw [Derivation.map_algebraMap, smul_zero]

private lemma  dlog_eq_of_isPrincipal_sub
  {K F : Type*}
  [Field K]
  [Field F]
  [Algebra K F]
  (p : ℕ) [CharP K p]
  (hconst : ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) → u ∈ (algebraMap K F).range)
  {D₁ D₂ : Divisor K F} (h : Divisor.IsPrincipal (D₁ - D₂))
  {f₁ f₂ : F} (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0)
  (h₀ : ∀ v : Place K F, (p : ℤ) * D₁ v = v.ord f₁)
  (h₁ : ∀ v : Place K F, (p : ℤ) * D₂ v = v.ord f₂) :
  f₁⁻¹ • D K F f₁ = f₂⁻¹ • D K F f₂ := by
  obtain ⟨h, hh, hDh⟩ := h
  have hhp : h ^ p ≠ 0 := pow_ne_zero _ hh
  set u : F := f₁ * (f₂ * h ^ p)⁻¹ with hu_def
  have hu0 : u ≠ 0 := mul_ne_zero hf₁ (inv_ne_zero (mul_ne_zero hf₂ hhp))
  have hu : ∀ v : Place K F, v.ord u = 0 := fun v => by
    rw [hu_def, v.ord_mul hf₁ (inv_ne_zero (mul_ne_zero hf₂ hhp)), v.ord_inv,
      v.ord_mul hf₂ hhp, ← h₀ v, ← h₁ v]
    have hp : v.ord (h ^ p) = (p : ℤ) * v.ord h := by
      rw [← zpow_natCast, v.ord_zpow]
    rw [hp, ← hDh v, Finsupp.sub_apply]
    ring
  obtain ⟨c, hc⟩ := hconst u hu0 hu
  have hf₁' : f₁ = algebraMap K F c * (f₂ * h ^ p) := by
    rw [hc, hu_def, inv_mul_cancel_right₀ (mul_ne_zero hf₂ hhp)]
  have hc0 : algebraMap K F c ≠ 0 := by rw [hc]; apply hu0
  rw [hf₁', dlog_mul hc0 (mul_ne_zero hf₂ hhp), dlog_algebraMap, zero_add, dlog_mul hf₂ hhp,
    D_pow_char p, smul_zero, add_zero]
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F]
  {p : ℕ} [CharP K p]
  {D₁ D₂ : AlgebraicCurve.Divisor K F}
  {f₁ f₂ : F}
-- given
  (hconst : ∀ u : F, u ≠ 0 → (∀ v : AlgebraicCurve.Place K F, v.ord u = 0) → u ∈ (algebraMap K F).range)
  (h : AlgebraicCurve.Divisor.IsPrincipal (D₁ - D₂))
  (hf₁ : f₁ ≠ 0)
  (hf₂ : f₂ ≠ 0)
  (h₀ : ∀ v : AlgebraicCurve.Place K F, (p : ℤ) * D₁ v = v.ord f₁)
  (h₁ : ∀ v : AlgebraicCurve.Place K F, (p : ℤ) * D₂ v = v.ord f₂) :
-- imply
  f₁⁻¹ • KaehlerDifferential.D K F f₁ = f₂⁻¹ • KaehlerDifferential.D K F f₂ :=
-- proof
  dlog_eq_of_isPrincipal_sub p hconst h hf₁ hf₂ h₀ h₁


-- created on 2026-10-23

