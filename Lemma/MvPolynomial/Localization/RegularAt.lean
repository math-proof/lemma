import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.Localization.RegularAt
open FractionRing
open MvPolynomial
open AffineCoordinateRing


/--
[isRegularAt_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Localization/RegularAt.lean)
-/
@[path]
private lemma isRegularAt_algebraMap_eq
  [CommRing A] [CommRing K] [Nontrivial K]
  {ev : A →+* K}
  {a : A} :
-- imply
  IsRegularAt ev (algebraMap A (FractionRing A) a) := by
-- proof
  apply FractionRing.isRegularAt_algebraMap ev a

/--
[isRegularAt_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Localization/RegularAt.lean)
-/
@[path]
private lemma isRegularAt_zero_eq
  [CommRing A] [CommRing K] [Nontrivial K]
  {ev : A →+* K} :
-- imply
  IsRegularAt ev 0 := by
-- proof
  apply FractionRing.isRegularAt_zero ev

/--
[isRegularAt_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Localization/RegularAt.lean)
-/
@[path]
private lemma isRegularAt_one_eq
  [CommRing A] [CommRing K] [Nontrivial K]
  {ev : A →+* K} :
-- imply
  IsRegularAt ev 1 := by
-- proof
  apply FractionRing.isRegularAt_one ev

/--
[evalAt_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Localization/RegularAt.lean)
-/
@[path]
private lemma evalAt_mk_eq
  [Field K]
  {X : Set (σ → K)}
  {P : X}
  {f : MvPolynomial σ K} :
-- imply
  evalAt X P (Ideal.Quotient.mk _ f) = MvPolynomial.aeval P.1 f := by
-- proof
  apply MvPolynomial.AffineCoordinateRing.evalAt_mk X P f

/--
[isRegularAt_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Localization/RegularAt.lean)
-/
@[path]
private lemma MvPolynomial_AffineCoordinateRing_isRegularAt_algebraMap_eq
  [CommRing A] [CommRing K] [Nontrivial K]
  {ev : A →+* K}
  {a : A} :
-- imply
  IsRegularAt ev (algebraMap A (FractionRing A) a) := by
-- proof
  apply MvPolynomial.AffineCoordinateRing.isRegularAt_algebraMap ev a


-- created on 2026-10-20
