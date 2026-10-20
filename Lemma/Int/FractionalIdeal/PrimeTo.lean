import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.FractionalIdeal.PrimeTo
open scoped nonZeroDivisors
open FractionalIdeal


/--
[nonZeroDivisors_le_comap_algebraMap_atPrime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/PrimeTo.lean)
-/
@[path]
private lemma nonZeroDivisors_le_comap_algebraMap_atPrime_eq
  [CommRing A] [IsDomain A]
  {p : Ideal A} [p.IsPrime] :
-- imply
  A⁰ ≤ Submonoid.comap (algebraMap A (Localization.AtPrime p))
    (Localization.AtPrime p)⁰ := by
-- proof
  apply FractionalIdeal.nonZeroDivisors_le_comap_algebraMap_atPrime p

/--
[isPrimeTo_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/PrimeTo.lean)
-/
@[path]
private lemma isPrimeTo_one_eq
  [CommRing A] [IsDomain A]
  {J : Ideal A} :
-- imply
  IsPrimeTo (1 : FractionalIdeal A⁰ (FractionRing A)) J := by
-- proof
  apply FractionalIdeal.isPrimeTo_one J

/--
[IsPrimeTo.mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/PrimeTo.lean)
-/
@[path]
private lemma IsPrimeTo_mul_eq
  [CommRing A] [IsDomain A]
  {I K : FractionalIdeal A⁰ (FractionRing A)}
  {J : Ideal A}
-- given
  (hI : I.IsPrimeTo J)
  (hK : K.IsPrimeTo J) :
-- imply
  (I * K).IsPrimeTo J := by
-- proof
  apply FractionalIdeal.IsPrimeTo.mul hI hK

/--
[IsPrimeTo.inv_unit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/PrimeTo.lean)
-/
@[path]
private lemma IsPrimeTo_inv_unit_eq
  [CommRing A] [IsDomain A]
  {u : (FractionalIdeal A⁰ (FractionRing A))ˣ}
  {J : Ideal A}
-- given
  (hu : (u : FractionalIdeal A⁰ (FractionRing A)).IsPrimeTo J) :
-- imply
  ((u⁻¹ : (FractionalIdeal A⁰ (FractionRing A))ˣ) :
    FractionalIdeal A⁰ (FractionRing A)).IsPrimeTo J := by
-- proof
  apply FractionalIdeal.IsPrimeTo.inv_unit hu

/--
[mem_unitsPrimeTo_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/PrimeTo.lean)
-/
@[path]
private lemma mem_unitsPrimeTo_iff_eq
  [CommRing A] [IsDomain A]
  {J : Ideal A}
  {u : (FractionalIdeal A⁰ (FractionRing A))ˣ} :
-- imply
  u ∈ unitsPrimeTo J ↔
    (u : FractionalIdeal A⁰ (FractionRing A)).IsPrimeTo J := by
-- proof
  apply FractionalIdeal.mem_unitsPrimeTo_iff

/--
[IsPrimeTo.mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/PrimeTo.lean)
-/
@[path]
private lemma IsPrimeTo_mono_eq
  [CommRing A] [IsDomain A]
  {I : FractionalIdeal A⁰ (FractionRing A)}
  {J K : Ideal A}
-- given
  (hI : I.IsPrimeTo J)
  (hJK : J ≤ K) :
-- imply
  I.IsPrimeTo K := by
-- proof
  apply FractionalIdeal.IsPrimeTo.mono hI hJK

/--
[unitsPrimeTo_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/PrimeTo.lean)
-/
@[path]
private lemma unitsPrimeTo_mono_eq
  [CommRing A] [IsDomain A]
  {J K : Ideal A}
-- given
  (hJK : J ≤ K) :
-- imply
  unitsPrimeTo J ≤ unitsPrimeTo K := by
-- proof
  apply FractionalIdeal.unitsPrimeTo_mono hJK

/--
[unitsPrimeTo_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/PrimeTo.lean)
-/
@[path]
private lemma unitsPrimeTo_top_eq
  [CommRing A] [IsDomain A] :
-- imply
  unitsPrimeTo (⊤ : Ideal A) = ⊤ := by
-- proof
  apply FractionalIdeal.unitsPrimeTo_top


-- created on 2026-10-20
