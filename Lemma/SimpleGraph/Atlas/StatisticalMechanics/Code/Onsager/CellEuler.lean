import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.CellEuler.Part3
open StatMech StatMech.Onsager StatMech.Onsager.CellEuler


/--
[cornerCount_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEuler.lean)
-/
@[path]
private lemma cornerCount_insert_eq
  {S : Finset (ℤ × ℤ)}
  {c : ℤ × ℤ}
  {v : ℤ × ℤ}
-- given
  (hc : c ∉ S) :
-- imply
  cornerCount (insert c S) v = cornerCount S v + (if v ∈ cornersOf c then 1 else 0) := by
-- proof
  apply StatMech.Onsager.CellEuler.cornerCount_insert S c hc v

/--
[cellVerts_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEuler.lean)
-/
@[path]
private lemma cellVerts_insert_eq
  {S : Finset (ℤ × ℤ)}
  {c : ℤ × ℤ} :
-- imply
  cellVerts (insert c S) = cornersOf c ∪ cellVerts S := by
-- proof
  apply StatMech.Onsager.CellEuler.cellVerts_insert S c

/--
[cornerCount_pos_iff_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEuler.lean)
-/
@[path]
private lemma cornerCount_pos_iff_mem_eq
  {S : Finset (ℤ × ℤ)}
  {v : ℤ × ℤ} :
-- imply
  0 < cornerCount S v ↔ v ∈ cellVerts S := by
-- proof
  apply StatMech.Onsager.CellEuler.cornerCount_pos_iff_mem S v

/--
[cornerWeight_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEuler.lean)
-/
@[path]
private lemma cornerWeight_zero_eq :
-- imply
  cornerWeight 0 = 0 := by
-- proof
  apply StatMech.Onsager.CellEuler.cornerWeight_zero

/--
[cornerDiff_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEuler.lean)
-/
@[path]
private lemma cornerDiff_eq_sum_eq
  {S : Finset (ℤ × ℤ)} :
-- imply
  cornerDiff S = ∑ v ∈ cellVerts S, cornerWeight (cornerCount S v) := by
-- proof
  apply StatMech.Onsager.CellEuler.cornerDiff_eq_sum S

/--
[cornerDiff_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEuler.lean)
-/
@[path]
private lemma cornerDiff_insert_eq
  {S : Finset (ℤ × ℤ)}
  {c : ℤ × ℤ}
-- given
  (hc : c ∉ S) :
-- imply
  cornerDiff (insert c S) = cornerDiff S + ∑ v ∈ cornersOf c, (cornerWeight (cornerCount S v + 1) - cornerWeight (cornerCount S v)) := by
-- proof
  apply StatMech.Onsager.CellEuler.cornerDiff_insert S c hc

/--
[cornerCount_singleton_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEuler.lean)
-/
@[path]
private lemma cornerCount_singleton_eq_one_eq
  {c v : ℤ × ℤ}
-- given
  (hv : v ∈ cornersOf c) :
-- imply
  cornerCount ({c} : Finset (ℤ × ℤ)) v = 1 := by
-- proof
  apply StatMech.Onsager.CellEuler.cornerCount_singleton_eq_one c v hv

/--
[cornerCount_singleton_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEuler.lean)
-/
@[path]
private lemma cornerCount_singleton_eq_zero_eq
  {c v : ℤ × ℤ}
-- given
  (hv : v ∉ cornersOf c) :
-- imply
  cornerCount ({c} : Finset (ℤ × ℤ)) v = 0 := by
-- proof
  apply StatMech.Onsager.CellEuler.cornerCount_singleton_eq_zero c v hv

/--
[cellVerts_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEuler.lean)
-/
@[path]
private lemma cellVerts_singleton_eq
  {c : ℤ × ℤ} :
-- imply
  cellVerts ({c} : Finset (ℤ × ℤ)) = cornersOf c := by
-- proof
  apply StatMech.Onsager.CellEuler.cellVerts_singleton c

/--
[cornerDiff_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEuler.lean)
-/
@[path]
private lemma cornerDiff_singleton_eq
  {c : ℤ × ℤ} :
-- imply
  cornerDiff ({c} : Finset (ℤ × ℤ)) = 4 := by
-- proof
  apply StatMech.Onsager.CellEuler.cornerDiff_singleton c

/--
[cornerCount_eq_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEuler.lean)
-/
@[path]
private lemma cornerCount_eq_inter_eq
  {S : Finset (ℤ × ℤ)}
  {v : ℤ × ℤ} :
-- imply
  cornerCount S v = (S ∩ ({v, (v.1 - 1, v.2), (v.1, v.2 - 1), (v.1 - 1, v.2 - 1)} : Finset (ℤ × ℤ))).card := by
-- proof
  apply StatMech.Onsager.CellEuler.cornerCount_eq_inter S v

/--
[edgesOf_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEuler.lean)
-/
@[path]
private lemma edgesOf_card_eq
  {c : ℤ × ℤ} :
-- imply
  (edgesOf c).card = 4 := by
-- proof
  apply StatMech.Onsager.CellEuler.edgesOf_card c

/--
[cellEdges_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEuler.lean)
-/
@[path]
private lemma cellEdges_insert_eq
  {S : Finset (ℤ × ℤ)}
  {c : ℤ × ℤ} :
-- imply
  cellEdges (insert c S) = edgesOf c ∪ cellEdges S := by
-- proof
  apply StatMech.Onsager.CellEuler.cellEdges_insert S c

/--
[cellEdges_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEuler.lean)
-/
@[path]
private lemma cellEdges_singleton_eq
  {c : ℤ × ℤ} :
-- imply
  cellEdges ({c} : Finset (ℤ × ℤ)) = edgesOf c := by
-- proof
  apply StatMech.Onsager.CellEuler.cellEdges_singleton c

/--
[eulerChar_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEuler.lean)
-/
@[path]
private lemma eulerChar_singleton_eq
  {c : ℤ × ℤ} :
-- imply
  eulerChar ({c} : Finset (ℤ × ℤ)) = 1 := by
-- proof
  apply StatMech.Onsager.CellEuler.eulerChar_singleton c

/--
[eulerChar_insert_vertexDelta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEuler.lean)
-/
@[path]
private lemma eulerChar_insert_vertexDelta_eq
  {S : Finset (ℤ × ℤ)}
  {c : ℤ × ℤ} :
-- imply
  ((cellVerts (insert c S)).card : ℤ) - (cellVerts S).card = ((cornersOf c \ cellVerts S).card : ℤ) := by
-- proof
  apply StatMech.Onsager.CellEuler.eulerChar_insert_vertexDelta S c

/--
[eulerChar_insert_edgeDelta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEuler.lean)
-/
@[path]
private lemma eulerChar_insert_edgeDelta_eq
  {S : Finset (ℤ × ℤ)}
  {c : ℤ × ℤ} :
-- imply
  ((cellEdges (insert c S)).card : ℤ) - (cellEdges S).card = ((edgesOf c \ cellEdges S).card : ℤ) := by
-- proof
  apply StatMech.Onsager.CellEuler.eulerChar_insert_edgeDelta S c

/--
[eulerChar_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEuler.lean)
-/
@[path]
private lemma eulerChar_insert_eq
  {S : Finset (ℤ × ℤ)}
  {c : ℤ × ℤ}
-- given
  (hc : c ∉ S) :
-- imply
  eulerChar (insert c S) = eulerChar S + (((cornersOf c \ cellVerts S).card : ℤ) - (edgesOf c \ cellEdges S).card + 1) := by
-- proof
  apply StatMech.Onsager.CellEuler.eulerChar_insert S c hc


-- created on 2026-10-23
