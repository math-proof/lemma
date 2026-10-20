import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.Polynomial.Eisenstein.AdjoinRoot
open Polynomial Ideal IsLocalRing
open AdjoinRoot


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
[irreducible_root_of_isEisensteinAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/Eisenstein/AdjoinRoot.lean)
-/
@[path]
private lemma irreducible_root_of_isEisensteinAt_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {f : A[X]}
-- given
  (heis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A))
  (hf : f.Monic)
  (hdeg : 0 < f.natDegree) :
-- imply
  Irreducible (root f) := by
-- proof
  apply AdjoinRoot.irreducible_root_of_isEisensteinAt f heis hf hdeg


-- created on 2026-10-20
