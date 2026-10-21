import Mathlib
import Lemma.Fin.CoeffRothLastSlice.eq.CoeffRothLastIndex.of.RothMvIndex
import Lemma.Fin.EqRothLastIndex.of.RothMvIndexAdd_1
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothLastSlice_zero_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
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
