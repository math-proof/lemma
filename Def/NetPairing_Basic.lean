import Mathlib

set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve.Affine.Point

universe u

section XCoord

variable {R : Type u} [CommRing R] {W : WeierstrassCurve.Affine R}

def xOrZero : W.Point → R
  | .zero => 0
  | .some x _ _ => x

end XCoord

variable {F : Type u} [Field F] {W : WeierstrassCurve.Affine F}

def netW20 : W.Point → F
  | .zero => 0
  | .some x y _ => y - W.negY x y


variable [DecidableEq F]

variable (P Q : W.Point)

noncomputable def netW21 : F := P.xOrZero - (P + Q).xOrZero

noncomputable def netW12 : F := Q.xOrZero - (P + Q).xOrZero

noncomputable def netW1m1 : F := Q.xOrZero - P.xOrZero

noncomputable def netW2m1 : F := (Q.xOrZero - P.xOrZero) ^ 2 * ((P - Q).xOrZero - P.xOrZero)

variable {P Q}

noncomputable def netCol (A B : W.Point) : ℕ → F
  | 0 => 1
  | 1 => 1
  | m + 2 =>
      netCol A B (m + 1) ^ 2 * (A.xOrZero - ((m + 1) • A + B).xOrZero) / netCol A B m


noncomputable def netPsi (P : W.Point) (n : ℕ) : F :=
  (W.preΨ (n : ℤ)).eval P.xOrZero * (if Even n then P.netW20 else 1)

noncomputable def netTau (p : ℕ) (P Q : W.Point) : F :=
  netCol P Q (p + 1) / P.netPsi (p + 1)

open scoped Classical in

noncomputable def netPairing (p : ℕ) (P Q : W.Point) : F :=
  if P ≠ 0 ∧ ∀ k : ℤ, Q ≠ k • P then netTau p P Q / netTau p Q P else 1


variable (W) in

def NetShearLaw (p : ℕ) : Prop :=
  ∀ ⦃P Q : W.Point⦄, p • P = 0 → p • Q = 0 → P ≠ 0 → (∀ k : ℤ, Q ≠ k • P) →
    netPairing p P (Q + P) = netPairing p P Q

variable (W) in

def NetScaleLaw (p : ℕ) : Prop :=
  ∀ ⦃P Q : W.Point⦄, p • P = 0 → p • Q = 0 → P ≠ 0 → (∀ k : ℤ, Q ≠ k • P) →
    ∀ a : ℕ, netPairing p P (a • Q) = netPairing p P Q ^ a

variable (W) in

def NetPairingNondegenerate (p : ℕ) : Prop :=
  ∃ P Q : W.Point, p • P = 0 ∧ p • Q = 0 ∧ netPairing p P Q ≠ 1

end WeierstrassCurve.Affine.Point
