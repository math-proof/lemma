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
public import Theorem.AlgebraicGeometry.EllipticCurve.NeronOggShafarevich

@[expose] public section

/-!
# The easy direction of the Néron–Ogg–Shafarevich criterion

This file proves that prime-to-residue-characteristic torsion of an elliptic curve with good
reduction is fixed by inertia, using the elementary valuation filtration at the origin.
-/


namespace MetaMathlibExt

open scoped WeierstrassCurve.Affine

def nosToValuationSubring {R k K : Type*} [CommRing R] [Field k] [Field K]
    [Algebra R k] [Algebra k K] (A : ValuationSubring K)
    (hA : (A.comap (algebraMap k K)).toSubring = (algebraMap R k).range) : R →+* A :=
  ((algebraMap k K).comp (algebraMap R k)).codRestrict A.toSubring fun r ↦ by
    apply nos_mem_of_mem_range A hA
    exact ⟨r, rfl⟩

end MetaMathlibExt
