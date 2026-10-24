import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.Localization.RegularAt
open FractionRing
open MvPolynomial
open AffineCoordinateRing


namespace FractionRing

/--
[isRegularAt_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Localization/RegularAt.lean)
-/
@[path]
lemma isRegularAt_algebraMap
  [CommRing A] [CommRing K] [Nontrivial K]
  {ev : A →+* K}
  {a : A} :
-- imply
  IsRegularAt ev (algebraMap A (FractionRing A) a) := by
-- proof
  refine ⟨1, by simp, ?_⟩
  simp

end FractionRing

namespace FractionRing

/--
[isRegularAt_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Localization/RegularAt.lean)
-/
@[path]
lemma isRegularAt_zero
  [CommRing A] [CommRing K] [Nontrivial K]
  {ev : A →+* K} :
-- imply
  IsRegularAt ev 0 := by
-- proof
  simpa only [map_zero] using isRegularAt_algebraMap ev 0

end FractionRing

namespace FractionRing

/--
[isRegularAt_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Localization/RegularAt.lean)
-/
@[path]
lemma isRegularAt_one
  [CommRing A] [CommRing K] [Nontrivial K]
  {ev : A →+* K} :
-- imply
  IsRegularAt ev 1 := by
-- proof
  simpa only [map_one] using isRegularAt_algebraMap ev 1
end FractionRing
namespace MvPolynomial


namespace MvPolynomial.AffineCoordinateRing

/--
[evalAt_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Localization/RegularAt.lean)
-/
@[path]
lemma evalAt_mk
  [Field K]
  {X : Set (σ → K)}
  {P : X}
  {f : MvPolynomial σ K} :
-- imply
  evalAt X P (Ideal.Quotient.mk _ f) = MvPolynomial.aeval P.1 f :=
-- proof
  Ideal.Quotient.lift_mk _ _ _

end MvPolynomial.AffineCoordinateRing

namespace MvPolynomial.AffineCoordinateRing

/--
[isRegularAt_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Localization/RegularAt.lean)
-/
@[path]
lemma isRegularAt_algebraMap
  [CommRing A] [CommRing K] [Nontrivial K]
  {ev : A →+* K}
  {a : A} :
-- imply
  IsRegularAt ev (algebraMap A (FractionRing A) a) :=
-- proof
  FractionRing.isRegularAt_algebraMap (evalAt X P) a
end MvPolynomial



-- created on 2026-10-20
-- updated on 2026-10-23
