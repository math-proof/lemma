import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.RingTheory.FractionalIdeal.PrimeTo.Part2
open scoped nonZeroDivisors
open FractionalIdeal


namespace FractionalIdeal

/--
[IsPrimeTo.mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/PrimeTo.lean)
-/
@[path]
lemma IsPrimeTo.mul
  [CommRing A] [IsDomain A]
  {I K : FractionalIdeal A⁰ (FractionRing A)}
  {J : Ideal A}
-- given
  (hI : I.IsPrimeTo J)
  (hK : K.IsPrimeTo J) :
-- imply
  (I * K).IsPrimeTo J := by
-- proof
  intro p _ hp
  rw [FractionalIdeal.extended_mul, hI p hp, hK p hp, one_mul]

end FractionalIdeal

namespace FractionalIdeal

/--
[IsPrimeTo.inv_unit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/PrimeTo.lean)
-/
@[path]
lemma IsPrimeTo.inv_unit
  [CommRing A] [IsDomain A]
  {u : (FractionalIdeal A⁰ (FractionRing A))ˣ}
  {J : Ideal A}
-- given
  (hu : (u : FractionalIdeal A⁰ (FractionRing A)).IsPrimeTo J) :
-- imply
  ((u⁻¹ : (FractionalIdeal A⁰ (FractionRing A))ˣ) :
    FractionalIdeal A⁰ (FractionRing A)).IsPrimeTo J := by
-- proof
  intro p _ hp
  have h1 : FractionalIdeal.extended (FractionRing A)
    (nonZeroDivisors_le_comap_algebraMap_atPrime p)
    (↑(u * u⁻¹) : FractionalIdeal A⁰ (FractionRing A)) = 1 := by
    simp [FractionalIdeal.extended_one]
  rwa [Units.val_mul, FractionalIdeal.extended_mul, hu p hp, one_mul] at h1

end FractionalIdeal

namespace FractionalIdeal

/--
[mem_unitsPrimeTo_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/PrimeTo.lean)
-/
@[path]
lemma mem_unitsPrimeTo_iff
  [CommRing A] [IsDomain A]
  {J : Ideal A}
  {u : (FractionalIdeal A⁰ (FractionRing A))ˣ} :
-- imply
  u ∈ unitsPrimeTo J ↔
    (u : FractionalIdeal A⁰ (FractionRing A)).IsPrimeTo J :=
-- proof
  Iff.rfl

end FractionalIdeal

namespace FractionalIdeal

/--
[IsPrimeTo.mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/PrimeTo.lean)
-/
@[path]
lemma IsPrimeTo.mono
  [CommRing A] [IsDomain A]
  {I : FractionalIdeal A⁰ (FractionRing A)}
  {J K : Ideal A}
-- given
  (hI : I.IsPrimeTo J)
  (hJK : J ≤ K) :
-- imply
  I.IsPrimeTo K := by
-- proof
  intro p _ hp
  exact hI p (hJK.trans hp)

end FractionalIdeal

namespace FractionalIdeal

/--
[unitsPrimeTo_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/PrimeTo.lean)
-/
@[path]
lemma unitsPrimeTo_mono
  [CommRing A] [IsDomain A]
  {J K : Ideal A}
-- given
  (hJK : J ≤ K) :
-- imply
  unitsPrimeTo J ≤ unitsPrimeTo K := by
-- proof
  intro u hu
  exact hu.mono hJK

end FractionalIdeal

namespace FractionalIdeal

/--
[unitsPrimeTo_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/PrimeTo.lean)
-/
@[path]
lemma unitsPrimeTo_top
  [CommRing A] [IsDomain A] :
-- imply
  unitsPrimeTo (⊤ : Ideal A) = ⊤ := by
-- proof
  rw [eq_top_iff]
  intro u _
  rw [mem_unitsPrimeTo_iff]
  intro p hpPrime hp
  exact (hpPrime.ne_top (top_unique hp)).elim

end FractionalIdeal

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


-- created on 2026-10-20
-- updated on 2026-10-26
