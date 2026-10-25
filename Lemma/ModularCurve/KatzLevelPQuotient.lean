import Mathlib
import Lemma.ModularCurve.KatzLevelP
import Def.ModularCurve_KatzLevelPQuotient

set_option autoImplicit false

noncomputable section

open WeierstrassCurve Polynomial

namespace ModularCurve

namespace LevelP

variable {A B : Type*} [CommRing A] [CommRing B] (W : WeierstrassCurve A)


theorem smulX_mul_ΨSq {a : ℤ} {x : A} (h : IsUnit ((W.ΨSq a).eval x)) :
    smulX W a x * (W.ΨSq a).eval x = (W.Φ a).eval x := by
  rw [smulX, mul_assoc, Ring.inverse_mul_cancel _ h, mul_one]

@[simp] theorem smulX_one (x : A) : smulX W 1 x = x := by
  simp [smulX, WeierstrassCurve.Φ_one, WeierstrassCurve.ΨSq_one]

theorem map_smulX (f : A →+* B) {a : ℤ} {x : A} (h : IsUnit ((W.ΨSq a).eval x)) :
    f (smulX W a x) = smulX (W.map f) a (f x) := by
  obtain ⟨u, hu⟩ := h
  rw [smulX, smulX, WeierstrassCurve.map_Φ, WeierstrassCurve.map_ΨSq, Polynomial.eval_map,
    Polynomial.eval_map, Polynomial.eval₂_at_apply, Polynomial.eval₂_at_apply, map_mul, ← hu,
    Ring.inverse_unit]
  change _ = _ * Ring.inverse ((Units.map (f : A →* B) u : Bˣ) : B)
  rw [Ring.inverse_unit]
  rfl

variable (p : ℕ)


variable (x : A)

@[simp] theorem quotientByLine_a₁ : (quotientByLine W p x).a₁ = W.a₁ := rfl
@[simp] theorem quotientByLine_a₂ : (quotientByLine W p x).a₂ = W.a₂ := rfl
@[simp] theorem quotientByLine_a₃ : (quotientByLine W p x).a₃ = W.a₃ := rfl
theorem quotientByLine_a₄ : (quotientByLine W p x).a₄ = W.a₄ - 5 * veluTLine W p x := rfl
theorem quotientByLine_a₆ :
    (quotientByLine W p x).a₆ = W.a₆ - W.b₂ * veluTLine W p x - 7 * veluWLine W p x := rfl

theorem quotientByLine_b₂ : (quotientByLine W p x).b₂ = W.b₂ := by
  simp [WeierstrassCurve.b₂]

theorem quotientByLine_b₄ : (quotientByLine W p x).b₄ = W.b₄ - 10 * veluTLine W p x := by
  simp only [WeierstrassCurve.b₄, quotientByLine_a₁, quotientByLine_a₃, quotientByLine_a₄]; ring

theorem quotientByLine_b₆ :
    (quotientByLine W p x).b₆ = W.b₆ - 4 * W.b₂ * veluTLine W p x - 28 * veluWLine W p x := by
  simp only [WeierstrassCurve.b₆, WeierstrassCurve.b₂, quotientByLine_a₃, quotientByLine_a₆]; ring

theorem quotientByLine_of_le_two (hp : p ≤ 2) : quotientByLine W p x = W := by
  have h0 : (p - 1) / 2 = 0 := by omega
  ext <;> simp [quotientByLine, veluTLine, veluWLine, h0]

theorem quotientByLine_map (f : A →+* B)
    (h : ∀ a ∈ Finset.Icc 1 ((p - 1) / 2), IsUnit ((W.ΨSq a).eval x)) :
    (quotientByLine W p x).map f = quotientByLine (W.map f) p (f x) := by
  have hT : f (veluTLine W p x) = veluTLine (W.map f) p (f x) := by
    simp only [veluTLine, map_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [map_add, map_add, map_mul, map_mul, map_pow, map_smulX W f (h a ha), WeierstrassCurve.map_b₂,
      WeierstrassCurve.map_b₄, map_ofNat]
  have hW : f (veluWLine W p x) = veluWLine (W.map f) p (f x) := by
    simp only [veluWLine, map_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hx := map_smulX W f (h a ha)
    simp only [map_add, map_mul, map_pow, hx, WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄,
      map_ofNat, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.map_b₆, eval_add, eval_mul, eval_pow,
      eval_C, eval_X, eval_ofNat]
  ext
  · simp [quotientByLine]
  · simp [quotientByLine]
  · simp [quotientByLine]
  · simp [quotientByLine, hT, map_ofNat]
  · simp [quotientByLine, hT, hW, map_ofNat]

end LevelP

namespace LevelPData

variable {A : Type*} [CommRing A] (W : WeierstrassCurve A) (p : ℕ) (D : LevelPData A)


@[simp] theorem quotientBySndLine_swap : D.swap.quotientBySndLine W p = D.quotientByFstLine W p := rfl

@[simp] theorem quotientByFstLine_swap : D.swap.quotientByFstLine W p = D.quotientBySndLine W p := rfl

theorem quotientBySndLine_eq : D.quotientBySndLine W p = LevelP.quotientByLine W p D.xQ := rfl

theorem quotientByFstLine_eq : D.quotientByFstLine W p = LevelP.quotientByLine W p D.xP := rfl

end LevelPData

end ModularCurve

end
