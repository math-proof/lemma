import Mathlib

set_option autoImplicit false

namespace WeierstrassCurve

open WeierstrassCurve.Affine

universe u v

variable {F : Type u} {k : Type v} [Field F] [Field k] (f : F →+* k) {W₀ : WeierstrassCurve F}

theorem Affine.Point.some_congr' {V : Affine k} {x₁ y₁ x₂ y₂ : k} (hx : x₁ = x₂)
    (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

def mapPoint : W₀.toAffine.Point → (W₀.map f).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (f x) (f y) ((W₀.toAffine.map_nonsingular f.injective x y).mpr h)

@[simp]
lemma mapPoint_zero : mapPoint f (0 : W₀.toAffine.Point) = 0 :=
  rfl

lemma mapPoint_some {x y : F} (h : W₀.toAffine.Nonsingular x y) :
    mapPoint f (.some x y h)
      = .some (f x) (f y) ((W₀.toAffine.map_nonsingular f.injective x y).mpr h) :=
  rfl

lemma mapPoint_injective : Function.Injective (mapPoint f (W₀ := W₀)) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · exact absurd h.symm (Affine.Point.some_ne_zero _)
  · exact absurd h (Affine.Point.some_ne_zero _)
  · rw [mapPoint_some, mapPoint_some, Affine.Point.some.injEq] at h
    exact Affine.Point.some_congr' (f.injective h.1) (f.injective h.2) _ _

theorem mapPoint_add [DecidableEq F] [DecidableEq k] (P Q : W₀.toAffine.Point) :
    mapPoint f (P + Q) = mapPoint f P + mapPoint f Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = W₀.toAffine.negY x₂ y₂
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2, mapPoint_zero, mapPoint_some,
      mapPoint_some,
      Affine.Point.add_of_Y_eq (congrArg f hxy.1) (by rw [hxy.2, Affine.map_negY])]
  · have hxy' : ¬(f x₁ = f x₂ ∧ f y₁ = (W₀.map f).toAffine.negY (f x₂) (f y₂)) := by
      rintro ⟨hx, hy⟩
      rw [Affine.map_negY] at hy
      exact hxy ⟨f.injective hx, f.injective hy⟩
    rw [Affine.Point.add_some hxy, mapPoint_some, mapPoint_some, mapPoint_some,
      Affine.Point.add_some hxy']
    exact Affine.Point.some_congr' (by rw [Affine.map_slope, Affine.map_addX])
      (by rw [Affine.map_slope, Affine.map_addY]) _ _

@[simps]
def mapPointHom [DecidableEq F] [DecidableEq k] :
    W₀.toAffine.Point →+ (W₀.map f).toAffine.Point where
  toFun := mapPoint f
  map_zero' := rfl
  map_add' := mapPoint_add f

lemma mapPointHom_injective [DecidableEq F] [DecidableEq k] :
    Function.Injective (mapPointHom f (W₀ := W₀)) :=
  mapPoint_injective f

theorem addOrderOf_mapPoint [DecidableEq F] [DecidableEq k] (P : W₀.toAffine.Point) :
    addOrderOf (mapPoint f P) = addOrderOf P :=
  addOrderOf_injective (mapPointHom f (W₀ := W₀)) (mapPoint_injective f) P

theorem addOrderOf_mapPoint_of_injective [DecidableEq F] [DecidableEq k]
    (_hf : Function.Injective f) (P : W₀.toAffine.Point) :
    addOrderOf (mapPoint f P) = addOrderOf P :=
  addOrderOf_mapPoint f P

theorem mapPoint_nsmul [DecidableEq F] [DecidableEq k] (n : ℕ) (P : W₀.toAffine.Point) :
    mapPoint f (n • P) = n • mapPoint f P :=
  map_nsmul (mapPointHom f (W₀ := W₀)) n P

theorem mapPoint_neg [DecidableEq F] [DecidableEq k] (P : W₀.toAffine.Point) :
    mapPoint f (-P) = -mapPoint f P :=
  map_neg (mapPointHom f (W₀ := W₀)) P

theorem Affine.Point.zero_heq_zero {V V' : Affine k} (hV : V' = V) :
    HEq (0 : V'.Point) (0 : V.Point) := by
  subst hV
  rfl

theorem Affine.Point.some_heq_some {V V' : Affine k} (hV : V' = V) {x y x' y' : k}
    {h : V.Nonsingular x y} {h' : V'.Nonsingular x' y'} (hx : x' = x) (hy : y' = y) :
    HEq (Point.some x' y' h' : V'.Point) (Point.some x y h : V.Point) := by
  subst hV
  subst hx
  subst hy
  rfl

theorem mapPoint_id_heq (V : WeierstrassCurve F) (P : V.toAffine.Point) :
    HEq (mapPoint (RingHom.id F) (W₀ := V) P) P := by
  have hV : V.map (RingHom.id F) = V := WeierstrassCurve.map_id V
  cases P with
  | zero => exact Affine.Point.zero_heq_zero hV.symm
  | some x y h => exact Affine.Point.some_heq_some hV.symm rfl rfl

universe w in

theorem mapPoint_comp_heq {k' : Type w} [Field k'] (σ : F →+* k) (τ : k →+* k')
    (V : WeierstrassCurve F) (P : V.toAffine.Point) :
    HEq (mapPoint (τ.comp σ) (W₀ := V) P) (mapPoint τ (W₀ := V.map σ) (mapPoint σ (W₀ := V) P)) := by
  have hV : (V.map σ).map τ = V.map (τ.comp σ) := WeierstrassCurve.map_map V σ τ
  cases P with
  | zero => exact Affine.Point.zero_heq_zero hV
  | some x y h => exact Affine.Point.some_heq_some hV rfl rfl

end WeierstrassCurve
