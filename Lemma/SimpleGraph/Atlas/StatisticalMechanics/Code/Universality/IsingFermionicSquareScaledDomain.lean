import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicSquareScaledDomain
open StatMech StatMech.Universality


/--
[fkIsingSquareWiredScaledDobrushinDomain_medialPosition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareScaledDomain.lean)
-/
@[path]
private lemma fkIsingSquareWiredScaledDobrushinDomain_medialPosition_eq
  {n : Nat}
  {mesh : Real}
  {a : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredScaledDobrushinDomain n hn mesh).medialPosition a = (mesh : Complex) * fkIsingSquareWiredCarrierPosition n hn a := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredScaledDobrushinDomain_medialPosition n hn mesh a

/--
[fkIsingSquareWiredScaledDobrushinDomain_fermionicObservable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareScaledDomain.lean)
-/
@[path]
private lemma fkIsingSquareWiredScaledDobrushinDomain_fermionicObservable_eq
  {n : Nat}
  {mesh : Real}
  {a : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredScaledDobrushinDomain n hn mesh).fermionicObservable a = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable a := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredScaledDobrushinDomain_fermionicObservable n hn mesh a

/--
[fkIsingSquareWiredScaledDobrushinDomain_normalizedFermionicObservable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareScaledDomain.lean)
-/
@[path]
private lemma fkIsingSquareWiredScaledDobrushinDomain_normalizedFermionicObservable_eq
  {n : Nat}
  {mesh : Real}
  {a : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredScaledDobrushinDomain n hn mesh).normalizedFermionicObservable mesh a = (fkIsingSquareWiredDobrushinDomain n hn).normalizedFermionicObservable mesh a := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredScaledDobrushinDomain_normalizedFermionicObservable n hn mesh a

/--
[fkIsingSquareWiredPerturbedCarrierPosition_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareScaledDomain.lean)
-/
@[path]
private lemma fkIsingSquareWiredPerturbedCarrierPosition_injective_eq
  {n : Nat}
  {mesh : Real}
-- given
  (hn : 0 < n)
  (hmesh : 0 < mesh) :
-- imply
  Function.Injective (fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPerturbedCarrierPosition_injective n hn mesh hmesh

/--
[fkIsingSquareWiredPerturbedCarrierPosition_dist_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareScaledDomain.lean)
-/
@[path]
private lemma fkIsingSquareWiredPerturbedCarrierPosition_dist_lt_eq
  {n : Nat}
  {mesh : Real}
  {a : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hmesh : 0 < mesh) :
-- imply
  dist (fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh a) ((mesh : Complex) * fkIsingSquareWiredCarrierPosition n hn a) < mesh / 10 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPerturbedCarrierPosition_dist_lt n hn mesh hmesh a

/--
[fkIsingSquareWiredPerturbedDobrushinDomain_fermionicObservable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareScaledDomain.lean)
-/
@[path]
private lemma fkIsingSquareWiredPerturbedDobrushinDomain_fermionicObservable_eq
  {n : Nat}
  {mesh : Real}
  {a : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hmesh : 0 < mesh) :
-- imply
  (fkIsingSquareWiredPerturbedDobrushinDomain n hn mesh hmesh).fermionicObservable a = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable a := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPerturbedDobrushinDomain_fermionicObservable n hn mesh hmesh a

/--
[fkIsingSquareWiredPerturbedRawInterpolant_medial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareScaledDomain.lean)
-/
@[path]
private lemma fkIsingSquareWiredPerturbedRawInterpolant_medial_eq
  {n : Nat}
  {mesh : Real}
  {a : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hmesh : 0 < mesh) :
-- imply
  fkIsingSquareWiredPerturbedRawInterpolant n hn mesh hmesh (fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh a) = (fkIsingSquareWiredPerturbedDobrushinDomain n hn mesh hmesh).fermionicObservable a := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPerturbedRawInterpolant_medial n hn mesh hmesh a


-- created on 2026-10-23
