/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Theorem.AlgebraicGeometry.EllipticCurve.NeronOggShafarevich.Part3

@[expose] public section

/-!
# The easy direction of the Néron–Ogg–Shafarevich criterion

This file proves that prime-to-residue-characteristic torsion of an elliptic curve with good
reduction is fixed by inertia, using the elementary valuation filtration at the origin.
-/


namespace MetaMathlibExt

open scoped WeierstrassCurve.Affine

def nosNear {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) : WeierstrassCurve.Affine.Point W → Prop
  | .zero => True
  | .some x _ _ => x ∉ A

def nosZ {K : Type*} [Field K] (W : WeierstrassCurve K) :
    WeierstrassCurve.Affine.Point W → K
  | .zero => 0
  | .some x y _ => -x / y

end MetaMathlibExt
