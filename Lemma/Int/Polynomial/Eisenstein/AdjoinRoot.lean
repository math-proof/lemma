import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.RingTheory.Polynomial.Eisenstein.AdjoinRoot
open Polynomial Ideal IsLocalRing
open AdjoinRoot


namespace AdjoinRoot

/--
[irreducible_root_of_isEisensteinAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/Eisenstein/AdjoinRoot.lean)
-/
@[path]
lemma irreducible_root_of_isEisensteinAt
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {f : A[X]}
-- given
  (heis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A))
  (hf : f.Monic)
  (hdeg : 0 < f.natDegree) :
-- imply
  Irreducible (root f) := by
-- proof
  have : IsDomain (AdjoinRoot f) := AdjoinRoot.isDomain_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp
      (heis.irreducible (IsLocalRing.maximalIdeal.isMaximal A).isPrime
        hf.isPrimitive hdeg))
  have : IsLocalRing (AdjoinRoot f) :=
    isLocalRing_of_isEisensteinAt f heis hf hdeg
  have : IsDiscreteValuationRing (AdjoinRoot f) :=
    isDiscreteValuationRing_of_isEisensteinAt f heis hf hdeg
  have : IsLocalRing.maximalIdeal (AdjoinRoot f) = Ideal.span {root f} :=
    isLocalRing_maximalIdeal_eq_span_root f heis hf hdeg
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr this

end AdjoinRoot

/--
[isMaximal_span_root](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/Eisenstein/AdjoinRoot.lean)
-/
@[path]
private lemma isMaximal_span_root_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {f : A[X]}
-- given
  (heis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A))
  (hf : f.Monic)
  (hdeg : 0 < f.natDegree) :
-- imply
  (Ideal.span {root f}).IsMaximal := by
-- proof
  apply AdjoinRoot.isMaximal_span_root f heis hf hdeg

/--
[root_mem_of_isMaximal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/Eisenstein/AdjoinRoot.lean)
-/
@[path]
private lemma root_mem_of_isMaximal_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {f : A[X]}
  {m : Ideal (AdjoinRoot f)}
-- given
  (heis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A))
  (hf : f.Monic)
  (hm : m.IsMaximal) :
-- imply
  root f ∈ m := by
-- proof
  apply AdjoinRoot.root_mem_of_isMaximal f heis hf m hm

/--
[isLocalRing_of_isEisensteinAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/Eisenstein/AdjoinRoot.lean)
-/
@[path]
private lemma isLocalRing_of_isEisensteinAt_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {f : A[X]}
-- given
  (heis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A))
  (hf : f.Monic)
  (hdeg : 0 < f.natDegree) :
-- imply
  IsLocalRing (AdjoinRoot f) := by
-- proof
  apply AdjoinRoot.isLocalRing_of_isEisensteinAt f heis hf hdeg

/--
[isLocalRing_maximalIdeal_eq_span_root](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/Eisenstein/AdjoinRoot.lean)
-/
@[path]
private lemma isLocalRing_maximalIdeal_eq_span_root_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {f : A[X]} [IsLocalRing (AdjoinRoot f)]
-- given
  (heis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A))
  (hf : f.Monic)
  (hdeg : 0 < f.natDegree) :
-- imply
  IsLocalRing.maximalIdeal (AdjoinRoot f) = Ideal.span {root f} := by
-- proof
  apply AdjoinRoot.isLocalRing_maximalIdeal_eq_span_root f heis hf hdeg

/--
[isDiscreteValuationRing_of_isEisensteinAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/Eisenstein/AdjoinRoot.lean)
-/
@[path]
private lemma isDiscreteValuationRing_of_isEisensteinAt_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {f : A[X]}
-- given
  (heis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A))
  (hf : f.Monic)
  (hdeg : 0 < f.natDegree) :
-- imply
  @IsDiscreteValuationRing (AdjoinRoot f) _
    (AdjoinRoot.isDomain_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (heis.irreducible (IsLocalRing.maximalIdeal.isMaximal A).isPrime
    hf.isPrimitive hdeg))) := by
-- proof
  apply AdjoinRoot.isDiscreteValuationRing_of_isEisensteinAt f heis hf hdeg

/--
[algebraMap_coeff_zero_mem_span_root](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/Eisenstein/AdjoinRoot.lean)
-/
@[path]
private lemma algebraMap_coeff_zero_mem_span_root_eq
  [CommRing A]
  {f : A[X]} :
-- imply
  algebraMap A (AdjoinRoot f) (f.coeff 0) ∈ Ideal.span {root f} := by
-- proof
  apply AdjoinRoot.algebraMap_coeff_zero_mem_span_root f

/--
[maximalIdeal_eq_span_coeff_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/Eisenstein/AdjoinRoot.lean)
-/
@[path]
private lemma maximalIdeal_eq_span_coeff_zero_eq
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {f : A[X]}
-- given
  (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal A))
  (hdeg : 0 < f.natDegree) :
-- imply
  IsLocalRing.maximalIdeal A = Ideal.span {f.coeff 0} := by
-- proof
  apply Polynomial.IsEisensteinAt.maximalIdeal_eq_span_coeff_zero f hf hdeg

/--
[map_maximalIdeal_le_span_root](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/Eisenstein/AdjoinRoot.lean)
-/
@[path]
private lemma map_maximalIdeal_le_span_root_eq
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {f : A[X]}
-- given
  (heis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A))
  (hdeg : 0 < f.natDegree) :
-- imply
  Ideal.map (algebraMap A (AdjoinRoot f)) (IsLocalRing.maximalIdeal A) ≤ Ideal.span {root f} := by
-- proof
  apply AdjoinRoot.map_maximalIdeal_le_span_root f heis hdeg

/--
[root_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/Eisenstein/AdjoinRoot.lean)
-/
@[path]
private lemma root_ne_zero_eq
  [CommRing A]
  [IsDomain A]
  [IsLocalRing A]
  {f : A[X]}
-- given
  (heis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A))
  (hf : f.Monic)
  (hdeg : 0 < f.natDegree) :
-- imply
  root f ≠ 0 := by
-- proof
  apply AdjoinRoot.root_ne_zero f heis hf hdeg


-- created on 2026-10-20
-- updated on 2026-10-26
