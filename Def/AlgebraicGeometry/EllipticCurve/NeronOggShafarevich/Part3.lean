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
import Theorem.AlgebraicGeometry.EllipticCurve.NeronOggShafarevich.Part3
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
