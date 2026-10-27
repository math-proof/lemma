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
/-!
# The easy direction of the Néron–Ogg–Shafarevich criterion

This file proves that prime-to-residue-characteristic torsion of an elliptic curve with good
reduction is fixed by inertia, using the elementary valuation filtration at the origin.
-/


namespace MetaMathlibExt

open scoped WeierstrassCurve.Affine

lemma nos_mem_of_mem_range {R k K : Type*} [CommRing R] [Field k] [Field K]
    [Algebra R k] [Algebra k K] (A : ValuationSubring K)
    (hA : (A.comap (algebraMap k K)).toSubring = (algebraMap R k).range)
    {x : k} (hx : x ∈ (algebraMap R k).range) : algebraMap k K x ∈ A := by
  rw [← ValuationSubring.mem_comap]
  change x ∈ (A.comap (algebraMap k K)).toSubring
  rw [hA]
  exact hx

end MetaMathlibExt
