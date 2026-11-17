module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

@[expose] public section

set_option autoImplicit false

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K]

section Formulas

variable (C : VariableChange K) (W : WeierstrassCurve.Affine K)

def vcX (x' : K) : K := (C.u : K) ^ 2 * x' + C.r

def vcY (x' y' : K) : K := (C.u : K) ^ 3 * y' + (C.u : K) ^ 2 * C.s * x' + C.t

def vcXInv (x : K) : K := ((C.u⁻¹ : Kˣ) : K) ^ 2 * (x - C.r)

def vcYInv (x y : K) : K := ((C.u⁻¹ : Kˣ) : K) ^ 3 * (y - C.t - C.s * (x - C.r))

variable {C W}

private lemma u_ne_zero : (C.u : K) ≠ 0 := C.u.ne_zero
private lemma u_pow_ne_zero (n : ℕ) : ((C.u : K)) ^ n ≠ 0 := pow_ne_zero n C.u.ne_zero

@[simp] lemma vcX_vcXInv (x : K) : vcX C (vcXInv C x) = x := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcX, vcXInv, Units.val_inv_eq_inv_val]; field_simp; ring

@[simp] lemma vcY_vcYInv (x y : K) : vcY C (vcXInv C x) (vcYInv C x y) = y := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcY, vcXInv, vcYInv, Units.val_inv_eq_inv_val]; field_simp; ring

@[simp] lemma vcXInv_vcX (x' : K) : vcXInv C (vcX C x') = x' := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcX, vcXInv, Units.val_inv_eq_inv_val]; field_simp; ring

@[simp] lemma vcYInv_vcY (x' y' : K) : vcYInv C (vcX C x') (vcY C x' y') = y' := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcX, vcY, vcYInv, Units.val_inv_eq_inv_val]; field_simp; ring

private lemma equation_aux (x' y' : K) :
    vcY C x' y' ^ 2 + W.a₁ * vcX C x' * vcY C x' y' + W.a₃ * vcY C x' y'
      - (vcX C x' ^ 3 + W.a₂ * vcX C x' ^ 2 + W.a₄ * vcX C x' + W.a₆)
    = (C.u : K) ^ 6 *
      (y' ^ 2 + (C • W).a₁ * x' * y' + (C • W).a₃ * y'
        - (x' ^ 3 + (C • W).a₂ * x' ^ 2 + (C • W).a₄ * x' + (C • W).a₆)) := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, Units.val_inv_eq_inv_val]
  field_simp; ring

private lemma partialX_aux (x' y' : K) :
    W.a₁ * vcY C x' y' - (3 * vcX C x' ^ 2 + 2 * W.a₂ * vcX C x' + W.a₄)
      + C.s * (2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃)
    = (C.u : K) ^ 4 *
      ((C • W).a₁ * y' - (3 * x' ^ 2 + 2 * (C • W).a₂ * x' + (C • W).a₄)) := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₂, variableChange_a₄,
    Units.val_inv_eq_inv_val]
  field_simp; ring

private lemma partialY_aux (x' y' : K) :
    2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃
      = (C.u : K) ^ 3 * (2 * y' + (C • W).a₁ * x' + (C • W).a₃) := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp; ring

lemma equation_variableChange_iff (x' y' : K) :
    (C • W).toAffine.Equation x' y' ↔ W.Equation (vcX C x') (vcY C x' y') := by
  rw [equation_iff', equation_iff', equation_aux x' y', mul_eq_zero,
    or_iff_right (u_pow_ne_zero 6)]

private lemma partials_zero_iff (x' y' : K) :
    ((C • W).a₁ * y' - (3 * x' ^ 2 + 2 * (C • W).a₂ * x' + (C • W).a₄) = 0
        ∧ 2 * y' + (C • W).a₁ * x' + (C • W).a₃ = 0)
      ↔ (W.a₁ * vcY C x' y' - (3 * vcX C x' ^ 2 + 2 * W.a₂ * vcX C x' + W.a₄) = 0
        ∧ 2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃ = 0) := by
  constructor
  · rintro ⟨hX', hY'⟩
    have hY : 2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃ = 0 := by
      rw [partialY_aux x' y', hY', mul_zero]
    refine ⟨?_, hY⟩
    have hX := partialX_aux (C := C) (W := W) x' y'
    rw [hX', mul_zero, hY, mul_zero, add_zero] at hX
    exact hX
  · rintro ⟨hX, hY⟩
    have hY' : 2 * y' + (C • W).a₁ * x' + (C • W).a₃ = 0 := by
      have h := partialY_aux (C := C) (W := W) x' y'
      rw [hY] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (u_pow_ne_zero 3)
    refine ⟨?_, hY'⟩
    have h := partialX_aux (C := C) (W := W) x' y'
    rw [hX, hY, mul_zero, add_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (u_pow_ne_zero 4)

lemma nonsingular_variableChange_iff (x' y' : K) :
    (C • W).toAffine.Nonsingular x' y' ↔ W.Nonsingular (vcX C x') (vcY C x' y') := by
  rw [nonsingular_iff', nonsingular_iff', equation_variableChange_iff x' y']
  refine and_congr_right fun _ => not_iff_not.mp ?_
  push_neg
  exact partials_zero_iff x' y'

end Formulas

section PointEquiv

variable [DecidableEq K] (C : VariableChange K) (W : WeierstrassCurve.Affine K)

namespace Point

def vcFun : (C • W).toAffine.Point → W.Point
  | 0 => 0
  | .some x' y' h => .some (vcX C x') (vcY C x' y')
      ((nonsingular_variableChange_iff x' y').mp h)

def vcInvFun : W.Point → (C • W).toAffine.Point
  | 0 => 0
  | .some x y h => .some (vcXInv C x) (vcYInv C x y)
      ((nonsingular_variableChange_iff (vcXInv C x) (vcYInv C x y)).mpr
        (by rwa [vcX_vcXInv, vcY_vcYInv]))

variable {C W}

@[simp] lemma vcFun_zero : vcFun C W 0 = 0 := rfl
@[simp] lemma vcInvFun_zero : vcInvFun C W 0 = 0 := rfl

private lemma some_eq_some {W' : WeierstrassCurve.Affine K} {x₁ y₁ x₂ y₂ : K}
    (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : W'.Nonsingular x₁ y₁} {h₂ : W'.Nonsingular x₂ y₂} :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by subst hx hy; rfl

lemma vcFun_leftInverse : Function.LeftInverse (vcInvFun C W) (vcFun C W) := by
  rintro (_ | ⟨x', y', h⟩)
  · rfl
  · simp only [vcFun, vcInvFun]
    exact some_eq_some (vcXInv_vcX x') (vcYInv_vcY x' y')

lemma vcFun_rightInverse : Function.RightInverse (vcInvFun C W) (vcFun C W) := by
  rintro (_ | ⟨x, y, h⟩)
  · rfl
  · simp only [vcFun, vcInvFun]
    exact some_eq_some (vcX_vcXInv x) (vcY_vcYInv x y)

variable (C W) in

noncomputable def variableChangeEquiv : (C • W).toAffine.Point ≃ W.Point :=
  ⟨vcFun C W, vcInvFun C W, vcFun_leftInverse, vcFun_rightInverse⟩

noncomputable def equivOfVariableChangeEq {V : WeierstrassCurve.Affine K}
    (h : C • W = V) : V.Point ≃ W.Point := by
  subst h; exact variableChangeEquiv C W

end Point

end PointEquiv

end WeierstrassCurve.Affine
