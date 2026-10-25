import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalPrimitiveBridge
open StatMech StatMech.Universality


/--
[fkIsingSquareWiredDirectedPhase_normSq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalPrimitiveBridge.lean)
-/
@[path]
private lemma fkIsingSquareWiredDirectedPhase_normSq_eq
  {n : Nat}
  {z : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  Complex.normSq (fkIsingSquareWiredDirectedPhase n hn z) = 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredDirectedPhase_normSq n hn z

/--
[fkIsingSquareWired_tangent_mul_observable_sq_eq_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalPrimitiveBridge.lean)
-/
@[path]
private lemma fkIsingSquareWired_tangent_mul_observable_sq_eq_increment_eq
  {n : Nat}
  {z : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredDirectedTangent n hn z * (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable z ^ 2 = (fkIsingSquareWiredPrimitiveIncrement n hn z : Complex) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_tangent_mul_observable_sq_eq_increment n hn z

/--
[fkIsingSquareWiredPrimitiveIncrement_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalPrimitiveBridge.lean)
-/
@[path]
private lemma fkIsingSquareWiredPrimitiveIncrement_nonneg_eq
  {n : Nat}
  {z : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  0 ≤ fkIsingSquareWiredPrimitiveIncrement n hn z := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPrimitiveIncrement_nonneg n hn z

/--
[fkIsingSquareWiredPrimitiveIncrement_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalPrimitiveBridge.lean)
-/
@[path]
private lemma fkIsingSquareWiredPrimitiveIncrement_le_one_eq
  {n : Nat}
  {z : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredPrimitiveIncrement n hn z ≤ 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPrimitiveIncrement_le_one n hn z

/--
[fkIsingSquareWiredPrimitiveIncrement_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalPrimitiveBridge.lean)
-/
@[path]
private lemma fkIsingSquareWiredPrimitiveIncrement_mem_Icc_eq
  {n : Nat}
  {z : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredPrimitiveIncrement n hn z ∈ Set.Icc 0 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPrimitiveIncrement_mem_Icc n hn z


-- created on 2026-10-23
