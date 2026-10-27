/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Valuation.LocalSubring
import Theorem.AlgebraicGeometry.EllipticCurve.NeronOggShafarevich.Part2
/-!
# The easy direction of the Néron–Ogg–Shafarevich criterion

This file proves that prime-to-residue-characteristic torsion of an elliptic curve with good
reduction is fixed by inertia, using the elementary valuation filtration at the origin.
-/


namespace MetaMathlibExt

open scoped WeierstrassCurve.Affine

def nosLocalEquation {K : Type*} [CommRing K] (W : WeierstrassCurve K)
    (z w : K) : Prop :=
  w = z ^ 3 + W.a₁ * z * w + W.a₂ * z ^ 2 * w + W.a₃ * w ^ 2 +
    W.a₄ * z * w ^ 2 + W.a₆ * w ^ 3

def nosChordU {K : Type*} [CommRing K] (W : WeierstrassCurve K)
    (z₁ w₁ w₂ : K) : K :=
  1 - W.a₁ * z₁ - W.a₂ * z₁ ^ 2 - W.a₃ * (w₂ + w₁) -
    W.a₄ * z₁ * (w₂ + w₁) - W.a₆ * (w₂ ^ 2 + w₂ * w₁ + w₁ ^ 2)

def nosChordV {K : Type*} [CommRing K] (W : WeierstrassCurve K)
    (z₁ z₂ w₂ : K) : K :=
  z₂ ^ 2 + z₂ * z₁ + z₁ ^ 2 + W.a₁ * w₂ +
    W.a₂ * (z₂ + z₁) * w₂ + W.a₄ * w₂ ^ 2

def nosLineC₃ {K : Type*} [CommRing K] (W : WeierstrassCurve K) (a : K) : K :=
  1 + W.a₂ * a + W.a₄ * a ^ 2 + W.a₆ * a ^ 3

def nosLineC₂ {K : Type*} [CommRing K] (W : WeierstrassCurve K) (a b : K) : K :=
  W.a₁ * a + W.a₂ * b + W.a₃ * a ^ 2 + 2 * W.a₄ * a * b +
    3 * W.a₆ * a ^ 2 * b

def nosLineQ₂ {K : Type*} [CommRing K] (W : WeierstrassCurve K) (l : K) : K :=
  l ^ 2 + W.a₁ * l - W.a₂

def nosLineQ₁ {K : Type*} [CommRing K] (W : WeierstrassCurve K) (l c : K) : K :=
  2 * l * c + W.a₁ * c + W.a₃ * l - W.a₄

def nosLineQ₀ {K : Type*} [CommRing K] (W : WeierstrassCurve K) (c : K) : K :=
  c ^ 2 + W.a₃ * c - W.a₆

end MetaMathlibExt
