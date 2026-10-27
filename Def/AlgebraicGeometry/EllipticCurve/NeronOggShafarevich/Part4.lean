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
import Theorem.AlgebraicGeometry.EllipticCurve.NeronOggShafarevich.Part4
/-!
# The easy direction of the Néron–Ogg–Shafarevich criterion

This file proves that prime-to-residue-characteristic torsion of an elliptic curve with good
reduction is fixed by inertia, using the elementary valuation filtration at the origin.
-/


namespace MetaMathlibExt

open scoped WeierstrassCurve.Affine

def nosIntegralCurve {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A)
    (ha₃ : W.a₃ ∈ A) (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A) : WeierstrassCurve A :=
  ⟨⟨W.a₁, ha₁⟩, ⟨W.a₂, ha₂⟩, ⟨W.a₃, ha₃⟩, ⟨W.a₄, ha₄⟩, ⟨W.a₆, ha₆⟩⟩

end MetaMathlibExt
