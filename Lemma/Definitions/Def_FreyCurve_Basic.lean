import Mathlib
import Lemma.Definitions.Def_FLTPrelim_FreyPackage

set_option autoImplicit false

namespace FreyCurve
open FreyPackage

lemma Δ (P : FreyPackage) : P.freyCurve.Δ = (P.a * P.b * P.c) ^ (2 * P.p) / 2 ^ 8 := by
  trans (P.a ^ P.p) ^ 2 * (P.b ^ P.p) ^ 2 * (P.c ^ P.p) ^ 2 / 2 ^ 8
  · field_simp
    norm_cast
    simp [← P.hFLT, WeierstrassCurve.Δ, freyCurve, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  · simp [← mul_pow, ← pow_mul, mul_comm 2]

instance (P : FreyPackage) : WeierstrassCurve.IsElliptic (freyCurve P) where
  isUnit := by
    rw [FreyCurve.Δ, isUnit_iff_ne_zero]
    apply div_ne_zero
    · norm_cast
      exact pow_ne_zero _ <| mul_ne_zero (mul_ne_zero P.ha0 P.hb0) P.hc0
    · norm_num

lemma b₂ (P : FreyPackage) : P.freyCurve.b₂ = P.b ^ P.p - P.a ^ P.p := by
  simp [freyCurve, WeierstrassCurve.b₂]; ring

lemma b₄ (P : FreyPackage) : P.freyCurve.b₄ = -(P.a * P.b) ^ P.p / 8 := by
  simp [freyCurve, WeierstrassCurve.b₄]; ring

lemma c₄ (P : FreyPackage) :
    P.freyCurve.c₄ = (P.a ^ P.p) ^ 2 + P.a ^ P.p * P.b ^ P.p + (P.b ^ P.p) ^ 2 := by
  simp [FreyCurve.b₂, FreyCurve.b₄, WeierstrassCurve.c₄]; ring

lemma c₄' (P : FreyPackage) :
    P.freyCurve.c₄ = P.c ^ (2 * P.p) - (P.a * P.b) ^ P.p := by
  rw [FreyCurve.c₄]
  have h : (P.a : ℚ) ^ P.p + (P.b : ℚ) ^ P.p = (P.c : ℚ) ^ P.p := by exact_mod_cast P.hFLT
  rw [pow_mul', ← h, mul_pow]; ring

end FreyCurve
