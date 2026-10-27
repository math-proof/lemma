import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.RSW.CrossingDuality.Part3
open Set SimpleGraph StatMech.Lattice StatMech.RSW.Box StatMech StatMech.RSW StatMech.RSW.CrossingDuality


/--
[rcd_crossingPair_incompatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/CrossingDuality.lean)
-/
@[path]
private lemma rcd_crossingPair_incompatible_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)} :
-- imply
  ¬ (ω e = true ∧ dualConfig ω (crossEdge e) = true) := by
-- proof
  apply StatMech.RSW.CrossingDuality.rcd_crossingPair_incompatible ω e

/--
[rcd_open_blocks_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/CrossingDuality.lean)
-/
@[path]
private lemma rcd_open_blocks_dual_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2}
  {w : (openSubgraph 2 ω).Walk x y}
  {x' y' : Site 2}
  {w' : (openSubgraph 2 (dualConfig ω)).Walk x' y'}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ w.edges)
  (he' : crossEdge e ∈ w'.edges) :
-- imply
  False := by
-- proof
  apply StatMech.RSW.CrossingDuality.rcd_open_blocks_dual ω w w' e he he'

/--
[rcd_mem_dualBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/CrossingDuality.lean)
-/
@[path]
private lemma rcd_mem_dualBox_eq
  {a b c d : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  ω ∈ rcd_dualBox a b c d ↔ DualVerticalCrossing ω (a + 1) (b - 1) c d := by
-- proof
  apply StatMech.RSW.CrossingDuality.rcd_mem_dualBox

/--
[rcd_leftReach_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/CrossingDuality.lean)
-/
@[path]
private lemma rcd_leftReach_subset_box_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a b c d : ℤ} :
-- imply
  rcd_leftReach ω a b c d ⊆ rect a b c d := by
-- proof
  apply StatMech.RSW.CrossingDuality.rcd_leftReach_subset_box ω a b c d

/--
[rcd_leftReach_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/CrossingDuality.lean)
-/
@[path]
private lemma rcd_leftReach_finite_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a b c d : ℤ} :
-- imply
  (rcd_leftReach ω a b c d).Finite := by
-- proof
  apply StatMech.RSW.CrossingDuality.rcd_leftReach_finite ω a b c d

/--
[rcd_horizontal_iff_right_in_leftReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/CrossingDuality.lean)
-/
@[path]
private lemma rcd_horizontal_iff_right_in_leftReach_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a b c d : ℤ} :
-- imply
  HorizontalCrossing ω a b c d ↔ ∃ y : Site 2, y ∈ rightSide a b c d ∧ y ∈ rcd_leftReach ω a b c d := by
-- proof
  apply StatMech.RSW.CrossingDuality.rcd_horizontal_iff_right_in_leftReach ω a b c d

/--
[rcd_no_horizontal_iff_right_unreachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/CrossingDuality.lean)
-/
@[path]
private lemma rcd_no_horizontal_iff_right_unreachable_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a b c d : ℤ} :
-- imply
  ¬ HorizontalCrossing ω a b c d ↔ ∀ y : Site 2, y ∈ rightSide a b c d → y ∉ rcd_leftReach ω a b c d := by
-- proof
  apply StatMech.RSW.CrossingDuality.rcd_no_horizontal_iff_right_unreachable ω a b c d

/--
[rcd_leftReach_extend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/CrossingDuality.lean)
-/
@[path]
private lemma rcd_leftReach_extend_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a b c d : ℤ}
  {v w : Site 2}
-- given
  (hv : v ∈ rcd_leftReach ω a b c d)
  (hwbox : w ∈ rect a b c d)
  (hadj : (hypercubicLattice 2).Adj v w)
  (hopen : ω s(v, w) = true) :
-- imply
  w ∈ rcd_leftReach ω a b c d := by
-- proof
  apply StatMech.RSW.CrossingDuality.rcd_leftReach_extend ω a b c d hv hwbox hadj hopen

/--
[rcd_leftReach_boundary_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/CrossingDuality.lean)
-/
@[path]
private lemma rcd_leftReach_boundary_closed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a b c d : ℤ}
  {v w : Site 2}
-- given
  (hv : v ∈ rcd_leftReach ω a b c d)
  (hwbox : w ∈ rect a b c d)
  (hadj : (hypercubicLattice 2).Adj v w)
  (hw : w ∉ rcd_leftReach ω a b c d) :
-- imply
  ω s(v, w) = false := by
-- proof
  apply StatMech.RSW.CrossingDuality.rcd_leftReach_boundary_closed ω a b c d hv hwbox hadj hw

/--
[rcd_leftReach_boundary_dual_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/CrossingDuality.lean)
-/
@[path]
private lemma rcd_leftReach_boundary_dual_open_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a b c d : ℤ}
  {v w : Site 2}
-- given
  (hv : v ∈ rcd_leftReach ω a b c d)
  (hwbox : w ∈ rect a b c d)
  (hadj : (hypercubicLattice 2).Adj v w)
  (hw : w ∉ rcd_leftReach ω a b c d) :
-- imply
  dualConfig ω (crossEdge s(v, w)) = true := by
-- proof
  apply StatMech.RSW.CrossingDuality.rcd_leftReach_boundary_dual_open ω a b c d hv hwbox hadj hw

/--
[rcd_leftReach_disjoint_rightSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/CrossingDuality.lean)
-/
@[path]
private lemma rcd_leftReach_disjoint_rightSide_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a b c d : ℤ}
-- given
  (hnoH : ¬ HorizontalCrossing ω a b c d) :
-- imply
  Disjoint (rcd_leftReach ω a b c d) (rightSide a b c d) := by
-- proof
  apply StatMech.RSW.CrossingDuality.rcd_leftReach_disjoint_rightSide ω a b c d hnoH

/--
[rcd_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/CrossingDuality.lean)
-/
@[path]
private lemma rcd_separation_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a b c d : ℤ}
-- given
  (hnoH : ¬ HorizontalCrossing ω a b c d) :
-- imply
  (rcd_leftReach ω a b c d).Finite ∧ (∀ x ∈ leftSide a b c d, x ∈ rcd_leftReach ω a b c d) ∧ Disjoint (rcd_leftReach ω a b c d) (rightSide a b c d) ∧ (∀ {v w : Site 2}, v ∈ rcd_leftReach ω a b c d → w ∈ rect a b c d → (hypercubicLattice 2).Adj v w → w ∉ rcd_leftReach ω a b c d → ω s(v, w) = false ∧ dualConfig ω (crossEdge s(v, w)) = true) := by
-- proof
  apply StatMech.RSW.CrossingDuality.rcd_separation ω a b c d hnoH


-- created on 2026-10-23
