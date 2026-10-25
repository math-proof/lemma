import Mathlib
import sympy.Basic
import Theorem.MathlibExtTest.RingTheory.Polynomial.Eisenstein.AdjoinRoot.Part3
open Polynomial ConcretePadicEisenstein


/--
[padicEisenstein_monic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/Polynomial/Eisenstein/AdjoinRoot.lean)
-/
@[path]
private lemma padicEisenstein_monic_eq
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {f : A[X]}
-- given
  (heis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A)) :
-- imply
  padicEisenstein.Monic := by
-- proof
  apply ConcretePadicEisenstein.padicEisenstein_monic f heis

/--
[padicEisenstein_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/Polynomial/Eisenstein/AdjoinRoot.lean)
-/
@[path]
private lemma padicEisenstein_natDegree_eq
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {f : A[X]}
-- given
  (heis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A)) :
-- imply
  padicEisenstein.natDegree = 2 := by
-- proof
  apply ConcretePadicEisenstein.padicEisenstein_natDegree f heis

/--
[padicEisenstein_natDegree_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/Polynomial/Eisenstein/AdjoinRoot.lean)
-/
@[path]
private lemma padicEisenstein_natDegree_pos_eq
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {f : A[X]}
-- given
  (heis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A)) :
-- imply
  0 < padicEisenstein.natDegree := by
-- proof
  apply ConcretePadicEisenstein.padicEisenstein_natDegree_pos f heis

/--
[padicEisenstein_isEisenstein](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/Polynomial/Eisenstein/AdjoinRoot.lean)
-/
@[path]
private lemma padicEisenstein_isEisenstein_eq
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {f : A[X]}
-- given
  (heis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A)) :
-- imply
  padicEisenstein.IsEisensteinAt (IsLocalRing.maximalIdeal PadicA) := by
-- proof
  apply ConcretePadicEisenstein.padicEisenstein_isEisenstein f heis


-- created on 2026-10-23
