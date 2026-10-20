/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Localization/RegularAt.lean -/

import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Nullstellensatz

/-!
# Regularity of rational functions at a point

This file defines regularity of a fraction-ring element relative to a ring-homomorphism
that evaluates denominators. It also specializes the definition to affine coordinate rings.
-/

namespace FractionRing

variable {A K : Type*} [CommRing A] [CommRing K]

/-- A fraction is regular at an evaluation when some nonvanishing denominator clears it. -/
def IsRegularAt (ev : A →+* K) (r : FractionRing A) : Prop :=
  ∃ g : A, ev g ≠ 0 ∧
    algebraMap A (FractionRing A) g * r ∈
      Set.range (algebraMap A (FractionRing A))

variable [Nontrivial K]

/-- Elements in the image of the base ring are regular at every evaluation. -/
theorem isRegularAt_algebraMap (ev : A →+* K) (a : A) :
    IsRegularAt ev (algebraMap A (FractionRing A) a) := by
  refine ⟨1, by simp, ?_⟩
  simp

/-- Zero is regular at every evaluation. -/
theorem isRegularAt_zero (ev : A →+* K) : IsRegularAt ev 0 := by
  simpa only [map_zero] using isRegularAt_algebraMap ev 0

/-- One is regular at every evaluation. -/
theorem isRegularAt_one (ev : A →+* K) : IsRegularAt ev 1 := by
  simpa only [map_one] using isRegularAt_algebraMap ev 1

end FractionRing

namespace MvPolynomial

variable {K σ : Type*} [Field K]

/-- The affine coordinate ring of a set of `K`-points. -/
abbrev AffineCoordinateRing (X : Set (σ → K)) :=
  MvPolynomial σ K ⧸ vanishingIdeal K X

namespace AffineCoordinateRing

/-- Evaluation of an affine coordinate-ring element at a point of the underlying set. -/
noncomputable def evalAt (X : Set (σ → K)) (P : X) : AffineCoordinateRing X →+* K :=
  Ideal.Quotient.lift _ (MvPolynomial.aeval (R := K) P.1)
    (fun _ hp ↦ (MvPolynomial.mem_vanishingIdeal_iff.mp hp) P.1 P.2)

/-- Evaluation of a residue class agrees with evaluation of its representative. -/
@[simp]
theorem evalAt_mk (X : Set (σ → K)) (P : X) (f : MvPolynomial σ K) :
    evalAt X P (Ideal.Quotient.mk _ f) = MvPolynomial.aeval P.1 f :=
  Ideal.Quotient.lift_mk _ _ _

/-- A rational function on an affine set is regular at a point when a denominator that
does not vanish there clears the function. -/
def IsRegularAt (X : Set (σ → K)) [IsDomain (AffineCoordinateRing X)]
    (r : FractionRing (AffineCoordinateRing X)) (P : X) : Prop :=
  FractionRing.IsRegularAt (evalAt X P) r

/-- Coordinate-ring elements define rational functions regular at every point. -/
theorem isRegularAt_algebraMap (X : Set (σ → K)) [IsDomain (AffineCoordinateRing X)]
    (a : AffineCoordinateRing X) (P : X) :
    IsRegularAt X (algebraMap (AffineCoordinateRing X)
      (FractionRing (AffineCoordinateRing X)) a) P :=
  FractionRing.isRegularAt_algebraMap (evalAt X P) a

end AffineCoordinateRing

end MvPolynomial
