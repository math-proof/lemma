module

public import Mathlib
public import Theorem.Fin.CoeffRothLastSlice.eq.CoeffRothLastIndex.of.RothMvIndex
public import Theorem.Fin.EqRothLastIndex_Last.of.RothMvIndex

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothLastSlice_natDegree_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.LeNatDegreeRothLastSlice.of.RothMvIndex
  {n : ℕ}
  {P : MvPolynomial (Fin (n + 1)) ℤ} {r : Fin (n + 1) → ℕ}
-- given
  (hP : rothDegreeBound P r)
  (i : RothMvIndex n) :
-- imply
  (rothLastSlice P i).natDegree ≤ r (Fin.last n) := by
-- proof
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro a ha
  rw [CoeffRothLastSlice.eq.CoeffRothLastIndex.of.RothMvIndex]
  by_contra hne
  have hmem : rothLastIndex i a ∈ P.support := MvPolynomial.mem_support_iff.mpr hne
  have hle := hP (rothLastIndex i a) hmem (Fin.last n)
  rw [EqRothLastIndex_Last.of.RothMvIndex] at hle
  omega


-- created on 2026-10-21
