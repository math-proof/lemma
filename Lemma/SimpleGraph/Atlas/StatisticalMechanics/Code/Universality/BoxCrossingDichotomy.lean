import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
open Set SimpleGraph StatMech.Lattice StatMech.RSW.Box StatMech StatMech.Universality


/--
[bcd_leftReach_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomy.lean)
-/
@[path]
private lemma bcd_leftReach_subset_box_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  bcd_leftReach ω n ⊆ rect 0 n 0 n := by
-- proof
  apply StatMech.Universality.bcd_leftReach_subset_box ω n

/--
[bcd_horizontal_iff_right_in_leftReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomy.lean)
-/
@[path]
private lemma bcd_horizontal_iff_right_in_leftReach_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  HorizontalCrossing ω 0 n 0 n ↔ ∃ y : Site 2, y ∈ rightSide 0 n 0 n ∧ y ∈ bcd_leftReach ω n := by
-- proof
  apply StatMech.Universality.bcd_horizontal_iff_right_in_leftReach ω n

/--
[bcd_no_horizontal_iff_right_unreachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomy.lean)
-/
@[path]
private lemma bcd_no_horizontal_iff_right_unreachable_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  ¬ HorizontalCrossing ω 0 n 0 n ↔ ∀ y : Site 2, y ∈ rightSide 0 n 0 n → y ∉ bcd_leftReach ω n := by
-- proof
  apply StatMech.Universality.bcd_no_horizontal_iff_right_unreachable ω n

/--
[bcd_leftReach_extend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomy.lean)
-/
@[path]
private lemma bcd_leftReach_extend_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {v w : Site 2}
-- given
  (hv : v ∈ bcd_leftReach ω n)
  (hwbox : w ∈ rect 0 n 0 n)
  (hadj : (hypercubicLattice 2).Adj v w)
  (hopen : ω s(v, w) = true) :
-- imply
  w ∈ bcd_leftReach ω n := by
-- proof
  apply StatMech.Universality.bcd_leftReach_extend ω n hv hwbox hadj hopen

/--
[bcd_leftReach_boundary_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomy.lean)
-/
@[path]
private lemma bcd_leftReach_boundary_closed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {v w : Site 2}
-- given
  (hv : v ∈ bcd_leftReach ω n)
  (hwbox : w ∈ rect 0 n 0 n)
  (hadj : (hypercubicLattice 2).Adj v w)
  (hw : w ∉ bcd_leftReach ω n) :
-- imply
  ω s(v, w) = false := by
-- proof
  apply StatMech.Universality.bcd_leftReach_boundary_closed ω n hv hwbox hadj hw

/--
[bcd_leftReach_boundary_dual_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomy.lean)
-/
@[path]
private lemma bcd_leftReach_boundary_dual_open_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {v w : Site 2}
-- given
  (hv : v ∈ bcd_leftReach ω n)
  (hwbox : w ∈ rect 0 n 0 n)
  (hadj : (hypercubicLattice 2).Adj v w)
  (hw : w ∉ bcd_leftReach ω n) :
-- imply
  dualConfig ω (crossEdge s(v, w)) = true := by
-- proof
  apply StatMech.Universality.bcd_leftReach_boundary_dual_open ω n hv hwbox hadj hw

/--
[bcd_leftReach_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomy.lean)
-/
@[path]
private lemma bcd_leftReach_finite_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  (bcd_leftReach ω n).Finite := by
-- proof
  apply StatMech.Universality.bcd_leftReach_finite ω n

/--
[bcd_leftReach_disjoint_rightSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomy.lean)
-/
@[path]
private lemma bcd_leftReach_disjoint_rightSide_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
-- imply
  Disjoint (bcd_leftReach ω n) (rightSide 0 n 0 n) := by
-- proof
  apply StatMech.Universality.bcd_leftReach_disjoint_rightSide ω n hnoH

/--
[bcd_crossing_edges_incompatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomy.lean)
-/
@[path]
private lemma bcd_crossing_edges_incompatible_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
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
  apply StatMech.Universality.bcd_crossing_edges_incompatible ω w w' e he he'

/--
[bcd_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomy.lean)
-/
@[path]
private lemma bcd_separation_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
-- imply
  (bcd_leftReach ω n).Finite ∧ (∀ x ∈ leftSide 0 n 0 n, x ∈ bcd_leftReach ω n) ∧ Disjoint (bcd_leftReach ω n) (rightSide 0 n 0 n) ∧ (∀ {v w : Site 2}, v ∈ bcd_leftReach ω n → w ∈ rect 0 n 0 n → (hypercubicLattice 2).Adj v w → w ∉ bcd_leftReach ω n → ω s(v, w) = false ∧ dualConfig ω (crossEdge s(v, w)) = true) := by
-- proof
  apply StatMech.Universality.bcd_separation ω n hnoH


-- created on 2026-10-23
