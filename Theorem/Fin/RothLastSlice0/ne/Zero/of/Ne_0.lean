module

public import Mathlib
public import Theorem.Fin.CoeffRothLastSlice.eq.CoeffRothLastIndex.of.RothMvIndex
public import Theorem.Fin.EqRothLastIndex.of.RothMvIndexAdd_1

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothLastSlice_zero_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothLastSlice0.ne.Zero.of.Ne_0
-- given
  (P : MvPolynomial (Fin 1) ℤ)
  (hP : P ≠ 0) :
-- imply
  rothLastSlice P (0 : RothMvIndex 0) ≠ 0 := by
-- proof
  intro hzero
  apply hP
  ext d
  have htail : rothLastTail d = (0 : RothMvIndex 0) := Subsingleton.elim _ _
  rw [← EqRothLastIndex.of.RothMvIndexAdd_1 d, htail,
    ← CoeffRothLastSlice.eq.CoeffRothLastIndex.of.RothMvIndex, hzero]
  simp


-- created on 2026-10-21
