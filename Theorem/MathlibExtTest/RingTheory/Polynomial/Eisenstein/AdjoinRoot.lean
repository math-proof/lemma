/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/Polynomial/Eisenstein/AdjoinRoot.lean -/

/-
Author: @toskua, Avocado
-/


import Theorem.RingTheory.Polynomial.Eisenstein.AdjoinRoot
import Lemma.Int.Polynomial.Eisenstein.AdjoinRoot
import Mathlib.NumberTheory.Padics.PadicIntegers
open Polynomial

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

variable (f : A[X]) (heis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A))
  (hf : f.Monic) (hdeg : 0 < f.natDegree)


-- The Eisenstein adjoint-root ring is local.
example : IsLocalRing (AdjoinRoot f) :=
  AdjoinRoot.isLocalRing_of_isEisensteinAt f heis hf hdeg

-- With that instance installed, the maximal-ideal equality is usable.
example : let _ := AdjoinRoot.isLocalRing_of_isEisensteinAt f heis hf hdeg
    IsLocalRing.maximalIdeal (AdjoinRoot f) =
    Ideal.span {AdjoinRoot.root f} := by
  dsimp only
  exact @AdjoinRoot.isLocalRing_maximalIdeal_eq_span_root _ _ _ _ f heis hf hdeg
    (AdjoinRoot.isLocalRing_of_isEisensteinAt f heis hf hdeg)

-- The exact DVR conclusion is usable, with its explicit domain instance.
example : @IsDiscreteValuationRing (AdjoinRoot f) _
    (AdjoinRoot.isDomain_of_prime
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp
        (heis.irreducible (IsLocalRing.maximalIdeal.isMaximal A).isPrime
          hf.isPrimitive hdeg))) :=
  AdjoinRoot.isDiscreteValuationRing_of_isEisensteinAt f heis hf hdeg

-- The root is irreducible (hence a uniformizer).
example : Irreducible (AdjoinRoot.root f) :=
  AdjoinRoot.irreducible_root_of_isEisensteinAt f heis hf hdeg

