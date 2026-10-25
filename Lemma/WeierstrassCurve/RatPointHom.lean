import Lemma.WeierstrassCurve.RatPointMap_probe

set_option autoImplicit false

namespace WeierstrassCurve

open WeierstrassCurve.Affine

variable {F k : Type} [Field F] [Field k] (f : F →+* k) {W₀ : WeierstrassCurve F}

theorem Affine.Point.some_congr {V : Affine k} {x₁ y₁ x₂ y₂ : k} (hx : x₁ = x₂)
    (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

@[simp]
lemma ratPointMap_zero : ratPointMap f (0 : W₀.toAffine.Point) = 0 :=
  rfl

lemma ratPointMap_some {x y : F} (h : W₀.toAffine.Nonsingular x y) :
    ratPointMap f (.some x y h)
      = .some (f x) (f y) ((W₀.toAffine.map_nonsingular f.injective x y).mpr h) :=
  rfl

lemma ratPointMap_injective : Function.Injective (ratPointMap f (W₀ := W₀)) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · exact absurd h.symm (Affine.Point.some_ne_zero _)
  · exact absurd h (Affine.Point.some_ne_zero _)
  · rw [ratPointMap_some, ratPointMap_some, Affine.Point.some.injEq] at h
    exact Affine.Point.some_congr (f.injective h.1) (f.injective h.2) _ _

theorem ratPointMap_add [DecidableEq F] [DecidableEq k] (P Q : W₀.toAffine.Point) :
    ratPointMap f (P + Q) = ratPointMap f P + ratPointMap f Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = W₀.toAffine.negY x₂ y₂
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2, ratPointMap_zero, ratPointMap_some,
      ratPointMap_some,
      Affine.Point.add_of_Y_eq (congrArg f hxy.1) (by rw [hxy.2, Affine.map_negY])]
  · have hxy' : ¬(f x₁ = f x₂ ∧ f y₁ = (W₀.map f).toAffine.negY (f x₂) (f y₂)) := by
      rintro ⟨hx, hy⟩
      rw [Affine.map_negY] at hy
      exact hxy ⟨f.injective hx, f.injective hy⟩
    rw [Affine.Point.add_some hxy, ratPointMap_some, ratPointMap_some, ratPointMap_some,
      Affine.Point.add_some hxy']
    exact Affine.Point.some_congr (by rw [Affine.map_slope, Affine.map_addX])
      (by rw [Affine.map_slope, Affine.map_addY]) _ _

@[simps]
def ratPointHom [DecidableEq F] [DecidableEq k] :
    W₀.toAffine.Point →+ (W₀.map f).toAffine.Point where
  toFun := ratPointMap f
  map_zero' := rfl
  map_add' := ratPointMap_add f

end WeierstrassCurve
