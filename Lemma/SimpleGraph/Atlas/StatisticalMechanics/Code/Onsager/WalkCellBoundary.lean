import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.WalkCellBoundary
open StatMech StatMech.Onsager StatMech.Onsager.WalkCellBoundary


/--
[imageGraph_not_adj_of_neighbours](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellBoundary.lean)
-/
@[path]
private lemma imageGraph_not_adj_of_neighbours_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {k : Fin (m + 3)}
  {q : Site 2}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hpred : q ≠ posSite d (k - 1))
  (hsucc : q ≠ posSite d (k + 1)) :
-- imply
  ¬ (imageGraph (walkP d hclosed hsimple)).Adj (posSite d k) q := by
-- proof
  apply StatMech.Onsager.WalkCellBoundary.imageGraph_not_adj_of_neighbours d hclosed hsimple k q hpred hsucc

/--
[leftCell_faceAdj_of_straight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellBoundary.lean)
-/
@[path]
private lemma leftCell_faceAdj_of_straight_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {k : Fin (m + 3)}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hstraight : d (k + 1) = d k) :
-- imply
  (walkRegionGraph d hclosed hsimple).Adj (cellFace (leftCell d k)) (cellFace (leftCell d (k + 1))) := by
-- proof
  apply StatMech.Onsager.WalkCellBoundary.leftCell_faceAdj_of_straight d hclosed hsimple k hstraight

/--
[leftCell_parity_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellBoundary.lean)
-/
@[path]
private lemma leftCell_parity_succ_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {k : Fin (m + 3)}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  rayParity d (leftCell d k).1 (leftCell d k).2 = rayParity d (leftCell d (k + 1)).1 (leftCell d (k + 1)).2 := by
-- proof
  apply StatMech.Onsager.WalkCellBoundary.leftCell_parity_succ d hclosed hsimple hreflexfree k

/--
[leftCell_parity_eq_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellBoundary.lean)
-/
@[path]
private lemma leftCell_parity_eq_of_reachable_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {i j : Fin (m + 3)}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
  (hreach : (cycleGraph (m + 3)).Reachable i j) :
-- imply
  rayParity d (leftCell d i).1 (leftCell d i).2 = rayParity d (leftCell d j).1 (leftCell d j).2 := by
-- proof
  apply StatMech.Onsager.WalkCellBoundary.leftCell_parity_eq_of_reachable d hclosed hsimple hreflexfree hreach

/--
[leftCell_parity_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellBoundary.lean)
-/
@[path]
private lemma leftCell_parity_one_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {k : Fin (m + 3)}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  rayParity d (leftCell d k).1 (leftCell d k).2 = 1 := by
-- proof
  apply StatMech.Onsager.WalkCellBoundary.leftCell_parity_one d hclosed hsimple hreflexfree k

/--
[leftCell_mem_interiorCells](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellBoundary.lean)
-/
@[path]
private lemma leftCell_mem_interiorCells_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {k : Fin (m + 3)}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  leftCell d k ∈ interiorCells d hclosed hsimple hreflexfree := by
-- proof
  apply StatMech.Onsager.WalkCellBoundary.leftCell_mem_interiorCells d hclosed hsimple hreflexfree k

/--
[walkRegion_flanking_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellBoundary.lean)
-/
@[path]
private lemma walkRegion_flanking_not_reachable_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {k : Fin (m + 3)}
  {f g : Site 2}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hlat : (hypercubicLattice 2).Adj f g)
  (hshared : sharedPrimalEdge f g = s(posSite d k, posSite d (k + 1))) :
-- imply
  ¬ (walkRegionGraph d hclosed hsimple).Reachable f g := by
-- proof
  apply StatMech.Onsager.WalkCellBoundary.walkRegion_flanking_not_reachable d hclosed hsimple k hlat hshared

/--
[left_right_flanking](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellBoundary.lean)
-/
@[path]
private lemma left_right_flanking_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {k : Fin (m + 3)}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0) :
-- imply
  (hypercubicLattice 2).Adj (cellFace (leftCell d k)) (cellFace (rightCell d k)) ∧ sharedPrimalEdge (cellFace (leftCell d k)) (cellFace (rightCell d k)) = s(posSite d k, posSite d (k + 1)) := by
-- proof
  apply StatMech.Onsager.WalkCellBoundary.left_right_flanking d hclosed k

/--
[rightCell_not_mem_interiorCells](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellBoundary.lean)
-/
@[path]
private lemma rightCell_not_mem_interiorCells_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {k : Fin (m + 3)}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  rightCell d k ∉ interiorCells d hclosed hsimple hreflexfree := by
-- proof
  apply StatMech.Onsager.WalkCellBoundary.rightCell_not_mem_interiorCells d hclosed hsimple hreflexfree k

/--
[cornerCount_eq_indicators](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellBoundary.lean)
-/
@[path]
private lemma cornerCount_eq_indicators_eq
  {m : ℕ}
  {S : Finset (ℤ × ℤ)}
  {v : ℤ × ℤ} :
-- imply
  cornerCount S v = (if v ∈ S then 1 else 0) + (if (v.1 - 1, v.2) ∈ S then 1 else 0) + (if (v.1, v.2 - 1) ∈ S then 1 else 0) + (if (v.1 - 1, v.2 - 1) ∈ S then 1 else 0) := by
-- proof
  apply StatMech.Onsager.WalkCellBoundary.cornerCount_eq_indicators S v

/--
[cornerCount_at_walkVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellBoundary.lean)
-/
@[path]
private lemma cornerCount_at_walkVertex_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {k : Fin (m + 3)}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  cornerCount (interiorCells d hclosed hsimple hreflexfree) (pos d (k + 1)) = if d (k + 1) - d k = 1 then 1 else 2 := by
-- proof
  apply StatMech.Onsager.WalkCellBoundary.cornerCount_at_walkVertex d hclosed hsimple hreflexfree k

/--
[cornerWeight_zero_of_not_walkVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellBoundary.lean)
-/
@[path]
private lemma cornerWeight_zero_of_not_walkVertex_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {v : ℤ × ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
  (hv : ∀ k : Fin (m + 3), pos d k ≠ v) :
-- imply
  cornerWeight (cornerCount (interiorCells d hclosed hsimple hreflexfree) v) = 0 := by
-- proof
  apply StatMech.Onsager.WalkCellBoundary.cornerWeight_zero_of_not_walkVertex d hclosed hsimple hreflexfree v hv

/--
[cornerWeight_at_walkVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellBoundary.lean)
-/
@[path]
private lemma cornerWeight_at_walkVertex_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {k : Fin (m + 3)}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  cornerWeight (cornerCount (interiorCells d hclosed hsimple hreflexfree) (pos d (k + 1))) = if d (k + 1) - d k = 1 then 1 else 0 := by
-- proof
  apply StatMech.Onsager.WalkCellBoundary.cornerWeight_at_walkVertex d hclosed hsimple hreflexfree k

/--
[cornerDiff_interiorCells_eq_cc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellBoundary.lean)
-/
@[path]
private lemma cornerDiff_interiorCells_eq_cc_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  cornerDiff (interiorCells d hclosed hsimple hreflexfree) = (cc d : ℤ) := by
-- proof
  apply StatMech.Onsager.WalkCellBoundary.cornerDiff_interiorCells_eq_cc d hclosed hsimple hreflexfree


-- created on 2026-10-23
