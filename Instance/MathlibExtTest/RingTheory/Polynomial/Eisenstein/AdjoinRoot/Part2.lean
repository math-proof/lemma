/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/Polynomial/Eisenstein/AdjoinRoot.lean -/

/-
Author: @toskua, Avocado
-/


import Theorem.RingTheory.Polynomial.Eisenstein.AdjoinRoot
import Lemma.Int.Polynomial.Eisenstein.AdjoinRoot
import Mathlib.NumberTheory.Padics.PadicIntegers
import Theorem.MathlibExtTest.RingTheory.Polynomial.Eisenstein.AdjoinRoot.Part2
open Polynomial

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

variable (f : A[X]) (heis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A))
  (hf : f.Monic) (hdeg : 0 < f.natDegree)


namespace ConcretePadicEisenstein

instance padicEisenstein_isDomain : IsDomain (AdjoinRoot padicEisenstein) :=
  AdjoinRoot.isDomain_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp
      (padicEisenstein_isEisenstein.irreducible
        (IsLocalRing.maximalIdeal.isMaximal PadicA).isPrime
        padicEisenstein_monic.isPrimitive padicEisenstein_natDegree_pos))

instance padicEisenstein_isLocalRing : IsLocalRing (AdjoinRoot padicEisenstein) :=
  AdjoinRoot.isLocalRing_of_isEisensteinAt
    padicEisenstein padicEisenstein_isEisenstein padicEisenstein_monic
      padicEisenstein_natDegree_pos

instance padicEisenstein_isDVR :
    IsDiscreteValuationRing (AdjoinRoot padicEisenstein) :=
  AdjoinRoot.isDiscreteValuationRing_of_isEisensteinAt
    padicEisenstein padicEisenstein_isEisenstein padicEisenstein_monic
      padicEisenstein_natDegree_pos

end ConcretePadicEisenstein
