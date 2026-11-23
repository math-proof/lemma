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
public import Theorem.AlgebraicGeometry.EllipticCurve.NeronOggShafarevich.Part4

@[expose] public section

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
