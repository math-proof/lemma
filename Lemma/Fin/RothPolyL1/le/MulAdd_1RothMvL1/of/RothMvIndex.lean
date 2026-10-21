import Mathlib
import Lemma.Fin.CoeffRothLastSlice.eq.CoeffRothLastIndex.of.RothMvIndex
import Lemma.Fin.LeNatDegreeRothLastSlice.of.RothMvIndex
import Lemma.Fin.NatAbsCoeff.le.RothMvL1.of.RothMvIndex
import Lemma.Polynomial.RothPolyL1.le.MulAddNatDegree1.of.All_LeNatAbsCoeff
open MathlibExt.NumberTheory.RothAuxiliary
open Fin
open Polynomial


/--
[rothPolyL1_lastSlice_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
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
