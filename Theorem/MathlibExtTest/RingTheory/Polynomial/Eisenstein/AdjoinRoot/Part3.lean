/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/Polynomial/Eisenstein/AdjoinRoot.lean -/

/-
Author: @toskua, Avocado
-/


import Theorem.RingTheory.Polynomial.Eisenstein.AdjoinRoot
import Lemma.Int.Polynomial.Eisenstein.AdjoinRoot
import Mathlib.NumberTheory.Padics.PadicIntegers
import Instance.MathlibExtTest.RingTheory.Polynomial.Eisenstein.AdjoinRoot.Part2
open Polynomial

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

variable (f : A[X]) (heis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A))
  (hf : f.Monic) (hdeg : 0 < f.natDegree)


namespace ConcretePadicEisenstein

-- The abstract maximal-ideal theorem computes the maximal ideal in this actual extension.
example : IsLocalRing.maximalIdeal (AdjoinRoot padicEisenstein) =
    Ideal.span {AdjoinRoot.root padicEisenstein} :=
  AdjoinRoot.isLocalRing_maximalIdeal_eq_span_root
    padicEisenstein padicEisenstein_isEisenstein padicEisenstein_monic
      padicEisenstein_natDegree_pos

-- The concrete extension is a DVR, and its root is a uniformizer.
example : IsDiscreteValuationRing (AdjoinRoot padicEisenstein) := inferInstance

example : Irreducible (AdjoinRoot.root padicEisenstein) :=
  AdjoinRoot.irreducible_root_of_isEisensteinAt
    padicEisenstein padicEisenstein_isEisenstein padicEisenstein_monic
      padicEisenstein_natDegree_pos

end ConcretePadicEisenstein
