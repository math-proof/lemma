module

public import Mathlib
public import Theorem.Fin.CoeffRothLastSlice.eq.CoeffRothLastIndex.of.RothMvIndex
public import Theorem.Fin.LeNatDegreeRothLastSlice.of.RothMvIndex
public import Theorem.Fin.NatAbsCoeff.le.RothMvL1.of.RothMvIndex
public import Theorem.Polynomial.RothPolyL1.le.MulAddNatDegree1.of.All_LeNatAbsCoeff

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Fin
open Polynomial


/--
[rothPolyL1_lastSlice_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothPolyL1.le.MulAdd_1RothMvL1.of.RothMvIndex
  {n : ℕ}
  {P : MvPolynomial (Fin (n + 1)) ℤ} {r : Fin (n + 1) → ℕ}
-- given
  (hP : rothDegreeBound P r)
  (i : RothMvIndex n) :
-- imply
  rothPolyL1 (rothLastSlice P i) ≤
    (r (Fin.last n) + 1) * rothMvL1 P :=
-- proof
  calc
    _ ≤ ((rothLastSlice P i).natDegree + 1) * rothMvL1 P :=
      RothPolyL1.le.MulAddNatDegree1.of.All_LeNatAbsCoeff _ _ fun a ↦ by
        rw [CoeffRothLastSlice.eq.CoeffRothLastIndex.of.RothMvIndex]
        exact NatAbsCoeff.le.RothMvL1.of.RothMvIndex P (rothLastIndex i a)
    _ ≤ (r (Fin.last n) + 1) * rothMvL1 P := by
      gcongr
      exact LeNatDegreeRothLastSlice.of.RothMvIndex hP i


-- created on 2026-10-21
