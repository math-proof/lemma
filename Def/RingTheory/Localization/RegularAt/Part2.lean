/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Localization/RegularAt.lean -/

module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Nullstellensatz
public import Abbrev.RingTheory.Localization.RegularAt

@[expose] public section

/-!
# Regularity of rational functions at a point

This file defines regularity of a fraction-ring element relative to a ring-homomorphism
that evaluates denominators. It also specializes the definition to affine coordinate rings.
-/


namespace MvPolynomial

namespace AffineCoordinateRing

/-- Evaluation of an affine coordinate-ring element at a point of the underlying set. -/
noncomputable def evalAt (X : Set (σ → K)) (P : X) : AffineCoordinateRing X →+* K :=
  Ideal.Quotient.lift _ (MvPolynomial.aeval (R := K) P.1)
    (fun _ hp ↦ (MvPolynomial.mem_vanishingIdeal_iff.mp hp) P.1 P.2)

/-- A rational function on an affine set is regular at a point when a denominator that
does not vanish there clears the function. -/
def IsRegularAt (X : Set (σ → K)) [IsDomain (AffineCoordinateRing X)]
    (r : FractionRing (AffineCoordinateRing X)) (P : X) : Prop :=
  FractionRing.IsRegularAt (evalAt X P) r

end AffineCoordinateRing
end MvPolynomial
