import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false

namespace RubinSilverberg

section KleinForms

variable {R : Type*} [CommRing R]

def kleinV (u : R) : R := u * (u ^ 10 + 11 * u ^ 5 - 1)

def kleinH (u : R) : R := u ^ 20 - 228 * u ^ 15 + 494 * u ^ 10 + 228 * u ^ 5 + 1

def kleinT (u : R) : R :=
  u ^ 30 + 522 * u ^ 25 - 10005 * u ^ 20 - 10005 * u ^ 10 - 522 * u ^ 5 + 1

def kleinVHom (n d : R) : R := n * d * (n ^ 10 + 11 * n ^ 5 * d ^ 5 - d ^ 10)

def kleinHHom (n d : R) : R :=
  n ^ 20 - 228 * n ^ 15 * d ^ 5 + 494 * n ^ 10 * d ^ 10 + 228 * n ^ 5 * d ^ 15 + d ^ 20

def kleinTHom (n d : R) : R :=
  n ^ 30 + 522 * n ^ 25 * d ^ 5 - 10005 * n ^ 20 * d ^ 10 - 10005 * n ^ 10 * d ^ 20
    - 522 * n ^ 5 * d ^ 25 + d ^ 30

end KleinForms

section KleinCurve

variable {K : Type*} [Field K]

def kleinCurve (u : K) : WeierstrassCurve K :=
  ⟨0, 0, 0, -kleinH u / 48, kleinT u / 864⟩

def kleinX (u : K) : K :=
  (u ^ 10 + 12 * u ^ 8 - 12 * u ^ 7 + 24 * u ^ 6 + 30 * u ^ 5 + 60 * u ^ 4 + 36 * u ^ 3
    + 24 * u ^ 2 + 12 * u + 1) / 12

def kleinY (u : K) : K :=
  (u ^ 13 + u ^ 12 + 4 * u ^ 11 + 5 * u ^ 9 + 6 * u ^ 8 + 21 * u ^ 7 + 29 * u ^ 6 + 25 * u ^ 5
    + 15 * u ^ 4 + 9 * u ^ 3 + 4 * u ^ 2 + u) / 2

noncomputable def pt (W : WeierstrassCurve K) (x y : K) : W.toAffine.Point :=
  open scoped Classical in
  if h : W.toAffine.Nonsingular x y then WeierstrassCurve.Affine.Point.some x y h else 0

theorem pt_eq_some {W : WeierstrassCurve K} {x y : K} (h : W.toAffine.Nonsingular x y) :
    pt W x y = WeierstrassCurve.Affine.Point.some x y h := by
  unfold pt
  exact dif_pos h

theorem pt_eq_zero {W : WeierstrassCurve K} {x y : K} (h : ¬ W.toAffine.Nonsingular x y) :
    pt W x y = 0 := by
  unfold pt
  exact dif_neg h

end KleinCurve

section Datum

variable {K : Type*} [Field K]

def rsBeta (u : K) : K :=
  kleinT u * (57 * u ^ 15 - 247 * u ^ 10 - 171 * u ^ 5 - 1)
    / (144 * u ^ 4 * (u ^ 10 + 11 * u ^ 5 - 1) ^ 4)

def rsGamma (u : K) : K :=
  kleinT u * (u ^ 15 - 171 * u ^ 10 + 247 * u ^ 5 + 57) / (144 * (u ^ 10 + 11 * u ^ 5 - 1) ^ 4)

def rsNum (u₀ l t : K) : K := (rsBeta u₀ + l * u₀) * t + u₀

def rsDen (u₀ l t : K) : K := (rsGamma u₀ + l) * t + 1

def rsFamilyA (a u₀ l t : K) : K :=
  a * kleinHHom (rsNum u₀ l t) (rsDen u₀ l t) / kleinH u₀

def rsFamilyB (b u₀ l t : K) : K :=
  b * kleinTHom (rsNum u₀ l t) (rsDen u₀ l t) / kleinT u₀

def rsMember (a b u₀ l t : K) : WeierstrassCurve K :=
  ⟨0, 0, 0, rsFamilyA a u₀ l t, rsFamilyB b u₀ l t⟩

def IsKleinDatum (a b u₀ : K) : Prop :=
  kleinH u₀ ^ 3 * (4 * a ^ 3 + 27 * b ^ 2) + 6912 * a ^ 3 * kleinV u₀ ^ 5 = 0 ∧ kleinV u₀ ≠ 0

end Datum

section Icosahedral

variable {K : Type*} [Field K]

def moeb (g : Matrix (Fin 2) (Fin 2) K) (u : K) : K := (g 0 0 * u + g 0 1) / (g 1 0 * u + g 1 1)

def moebDen (g : Matrix (Fin 2) (Fin 2) K) (u : K) : K := g 1 0 * u + g 1 1

def moebNum (g : Matrix (Fin 2) (Fin 2) K) (u : K) : K := g 0 0 * u + g 0 1

theorem moeb_eq_div (g : Matrix (Fin 2) (Fin 2) K) (u : K) : moeb g u = moebNum g u / moebDen g u := rfl

def sqrtFive (ζ : K) : K := ζ + ζ ^ 4 - ζ ^ 2 - ζ ^ 3

def icoS (ζ : K) : Matrix (Fin 2) (Fin 2) K := !![ζ ^ 3, 0; 0, ζ ^ 2]

def icoT : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, 0]

def icoU (ζ : K) : Matrix (Fin 2) (Fin 2) K :=
  (sqrtFive ζ)⁻¹ • !![-(ζ - ζ ^ 4), ζ ^ 2 - ζ ^ 3; ζ ^ 2 - ζ ^ 3, ζ - ζ ^ 4]

def IsIcoSymmetry (g : Matrix (Fin 2) (Fin 2) K) : Prop :=
  g.det = 1 ∧
  (∀ n d : K, kleinVHom (g 0 0 * n + g 0 1 * d) (g 1 0 * n + g 1 1 * d) = kleinVHom n d) ∧
  (∀ n d : K, kleinHHom (g 0 0 * n + g 0 1 * d) (g 1 0 * n + g 1 1 * d) = kleinHHom n d) ∧
  (∀ n d : K, kleinTHom (g 0 0 * n + g 0 1 * d) (g 1 0 * n + g 1 1 * d) = kleinTHom n d) ∧
  (∀ u : K, kleinV u ≠ 0 → moebDen g u ≠ 0 →
    moebDen g u * rsBeta (moeb g u) = g 0 0 * rsBeta u + g 0 1 * rsGamma u ∧
    moebDen g u * rsGamma (moeb g u) = g 1 0 * rsBeta u + g 1 1 * rsGamma u)

end Icosahedral

end RubinSilverberg
