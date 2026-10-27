import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.CellPinch
open StatMech StatMech.Onsager StatMech.Onsager.CellPinch


/--
[pinchAt_mem_cellVerts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellPinch.lean)
-/
@[path]
private lemma pinchAt_mem_cellVerts_eq
  {S : Finset (ℤ × ℤ)}
  {v : ℤ × ℤ}
-- given
  (h : pinchAt S v) :
-- imply
  v ∈ cellVerts S := by
-- proof
  apply StatMech.Onsager.CellPinch.pinchAt_mem_cellVerts S v h

/--
[pinchAt_insert_of_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellPinch.lean)
-/
@[path]
private lemma pinchAt_insert_of_notMem_eq
  {S : Finset (ℤ × ℤ)}
  {c v : ℤ × ℤ}
-- given
  (hv : v ∉ cornersOf c) :
-- imply
  pinchAt (insert c S) v = pinchAt S v := by
-- proof
  apply StatMech.Onsager.CellPinch.pinchAt_insert_of_notMem S c v hv

/--
[pinchW_zero_of_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellPinch.lean)
-/
@[path]
private lemma pinchW_zero_of_notMem_eq
  {S : Finset (ℤ × ℤ)}
  {v : ℤ × ℤ}
-- given
  (hv : v ∉ cellVerts S) :
-- imply
  pinchW S v = 0 := by
-- proof
  apply StatMech.Onsager.CellPinch.pinchW_zero_of_notMem S v hv

/--
[pinchCount_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellPinch.lean)
-/
@[path]
private lemma pinchCount_insert_eq
  {S : Finset (ℤ × ℤ)}
  {c : ℤ × ℤ}
-- given
  (hc : c ∉ S) :
-- imply
  pinchCount (insert c S) = pinchCount S + ∑ v ∈ cornersOf c, (pinchW (insert c S) v - pinchW S v) := by
-- proof
  apply StatMech.Onsager.CellPinch.pinchCount_insert S c hc


-- created on 2026-10-23
