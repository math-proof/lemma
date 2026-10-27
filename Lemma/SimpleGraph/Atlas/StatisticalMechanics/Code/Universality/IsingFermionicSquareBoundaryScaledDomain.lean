import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryScaledDomain.Part3
open StatMech StatMech.Universality


/--
[fkIsingSquareBoundaryPerturbedDobrushinDomain_fermionicObservable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryScaledDomain.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryPerturbedDobrushinDomain_fermionicObservable_eq
  {n : Nat}
  {mesh : Real}
  {a : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hmesh : 0 < mesh) :
-- imply
  (fkIsingSquareBoundaryPerturbedDobrushinDomain n hn mesh hmesh).fermionicObservable a = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable a := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryPerturbedDobrushinDomain_fermionicObservable n hn mesh hmesh a

/--
[fkIsingSquareBoundaryPerturbedRawInterpolant_medial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryScaledDomain.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryPerturbedRawInterpolant_medial_eq
  {n : Nat}
  {mesh : Real}
  {a : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hmesh : 0 < mesh) :
-- imply
  fkIsingSquareBoundaryPerturbedRawInterpolant n hn mesh hmesh (fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh a) = (fkIsingSquareBoundaryPerturbedDobrushinDomain n hn mesh hmesh).fermionicObservable a := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryPerturbedRawInterpolant_medial n hn mesh hmesh a

/--
[fkIsingSquareBoundaryPerturbedHolomorphicInterpolant_medial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryScaledDomain.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryPerturbedHolomorphicInterpolant_medial_eq
  {n : Nat}
  {mesh : Real}
  {a : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hmesh : 0 < mesh) :
-- imply
  fkIsingSquareBoundaryPerturbedHolomorphicInterpolant n hn mesh hmesh (fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh a) = (fkIsingSquareBoundaryPerturbedDobrushinDomain n hn mesh hmesh).fermionicObservable a := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryPerturbedHolomorphicInterpolant_medial n hn mesh hmesh a

/--
[fkIsingSquareBoundaryPerturbedHolomorphicInterpolant_differentiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryScaledDomain.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryPerturbedHolomorphicInterpolant_differentiable_eq
  {n : Nat}
  {mesh : Real}
-- given
  (hn : 0 < n)
  (hmesh : 0 < mesh) :
-- imply
  Differentiable Complex (fkIsingSquareBoundaryPerturbedHolomorphicInterpolant n hn mesh hmesh) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryPerturbedHolomorphicInterpolant_differentiable n hn mesh hmesh


-- created on 2026-10-23
