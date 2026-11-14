import Mathlib
import Def.NetPairing_Basic

set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve.Affine.Point

universe u

section XCoord

variable {R : Type u} [CommRing R] {W : WeierstrassCurve.Affine R}


@[simp] lemma xOrZero_zero : (0 : W.Point).xOrZero = 0 := rfl

@[simp] lemma xOrZero_some {x y : R} (h : W.Nonsingular x y) :
    (Point.some x y h).xOrZero = x := rfl

end XCoord

variable {F : Type u} [Field F] {W : WeierstrassCurve.Affine F}


@[simp] lemma netW20_zero : (0 : W.Point).netW20 = 0 := rfl

@[simp] lemma netW20_some {x y : F} (h : W.Nonsingular x y) :
    (Point.some x y h).netW20 = y - W.negY x y := rfl

variable [DecidableEq F]

variable (P Q : W.Point)


variable {P Q}


@[simp] lemma netCol_zero : netCol P Q 0 = 1 := rfl
@[simp] lemma netCol_one : netCol P Q 1 = 1 := rfl


@[simp] lemma netPairing_zero_left (p : ℕ) (Q : W.Point) :
    netPairing p (0 : W.Point) Q = 1 := by
  unfold netPairing; rw [if_neg]; simp

@[simp] lemma netPairing_zero_right (p : ℕ) (P : W.Point) :
    netPairing p P (0 : W.Point) = 1 := by
  unfold netPairing
  by_cases hP : P = 0
  · rw [if_neg]; simp [hP]
  · rw [if_neg]; rintro ⟨_, h⟩; exact h 0 (by rw [zero_zsmul])

end WeierstrassCurve.Affine.Point
