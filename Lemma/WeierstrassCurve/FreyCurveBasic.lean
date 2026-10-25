import Mathlib
import Lemma.FLTPrelim.FreyPackage

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
