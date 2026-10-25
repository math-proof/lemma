import Mathlib
import Lemma.WeierstrassCurve.AddFormula
import Def.NetPairing_Basic
import Structure.TateCurve_XMultAlignment
import Macro.WeierstrassCurve_DivPolyMulFormula

set_option autoImplicit false

open Polynomial
open scoped WeierstrassCurve.DivPolyMulFormula

universe u


open Polynomial WeierstrassCurve


open Polynomial


open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

section Statement

def MFred (m : ℕ) {x y : F} (h : W.toAffine.Nonsingular x y) : Prop :=
  (W.ΨSq (m : ℤ)).eval x ≠ 0 ∧
    (m • (Point.some x y h : W.toAffine.Point)).xOrZero * (W.ΨSq (m : ℤ)).eval x =
      (W.Φ (m : ℤ)).eval x

def LowTorsionFree (m : ℕ) {x y : F} (h : W.toAffine.Nonsingular x y) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ m → k • (Point.some x y h : W.toAffine.Point) ≠ 0

end Statement

end WeierstrassCurve.Affine

open Polynomial

namespace WeierstrassCurve

section StarIdentityDef

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

def StarIdentity (j : ℤ) : Prop :=
  ∀ t : R,
    2 * t * (W.Φ j).eval t * ((W.Φ j).eval t + t * (W.ΨSq j).eval t) +
        W.b₂ * t * ((W.Φ j).eval t * (W.ΨSq j).eval t) +
        W.b₄ * (((W.Φ j).eval t + t * (W.ΨSq j).eval t) * (W.ΨSq j).eval t) +
        W.b₆ * (W.ΨSq j).eval t ^ 2 =
      (W.Φ (j + 1)).eval t * (W.ΨSq (j - 1)).eval t +
        (W.Φ (j - 1)).eval t * (W.ΨSq (j + 1)).eval t

end StarIdentityDef

end WeierstrassCurve
