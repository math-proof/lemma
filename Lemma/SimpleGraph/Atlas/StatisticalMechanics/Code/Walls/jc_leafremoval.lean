import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc_leafremoval.Part2
open SimpleGraph StatMech StatMech.Walls


/--
[jc_pendant_existsUnique_induce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_leafremoval.lean)
-/
@[path]
private lemma jc_pendant_existsUnique_induce_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : c ∈ K)
  (h : ∃! u : Site 2, u ∈ K ∧ (hypercubicLattice 2).Adj c u) :
-- imply
  ∃! u : ↑K, ((hypercubicLattice 2).induce K).Adj ⟨c, hc⟩ u := by
-- proof
  apply StatMech.Walls.jc_pendant_existsUnique_induce K c hc h

/--
[jc_pendant_nbr_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_leafremoval.lean)
-/
@[path]
private lemma jc_pendant_nbr_finite_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : c ∈ K)
  (h : ∃! u : ↑K, ((hypercubicLattice 2).induce K).Adj ⟨c, hc⟩ u) :
-- imply
  (((hypercubicLattice 2).induce K).neighborSet ⟨c, hc⟩).Finite := by
-- proof
  apply StatMech.Walls.jc_pendant_nbr_finite K c hc h

/--
[jc_cellConnected_diff_of_pendant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_leafremoval.lean)
-/
@[path]
private lemma jc_cellConnected_diff_of_pendant_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hconn : CellConnected K)
  (hpend : jc_IsPendantCell K c) :
-- imply
  CellConnected (K \ {c}) := by
-- proof
  apply StatMech.Walls.jc_cellConnected_diff_of_pendant K c hconn hpend

/--
[jc_leafRemoval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_leafremoval.lean)
-/
@[path]
private lemma jc_leafRemoval_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : c ∈ K)
  (hconn : CellConnected K)
  (hunique : ∃! u : Site 2, u ∈ K ∧ (hypercubicLattice 2).Adj c u) :
-- imply
  CellConnected (K \ {c}) := by
-- proof
  apply StatMech.Walls.jc_leafRemoval K c hc hconn hunique

/--
[jc_mem_domino](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_leafremoval.lean)
-/
@[path]
private lemma jc_mem_domino_eq
  {v : Site 2} :
-- imply
  v ∈ jc_domino ↔ v = ![0, 0] ∨ v = ![1, 0] := by
-- proof
  apply StatMech.Walls.jc_mem_domino v

/--
[jc_domino_00](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_leafremoval.lean)
-/
@[path]
private lemma jc_domino_00_eq :
-- imply
  (![0, 0] : Site 2) ∈ jc_domino := by
-- proof
  apply StatMech.Walls.jc_domino_00

/--
[jc_domino_10](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_leafremoval.lean)
-/
@[path]
private lemma jc_domino_10_eq :
-- imply
  (![1, 0] : Site 2) ∈ jc_domino := by
-- proof
  apply StatMech.Walls.jc_domino_10

/--
[jc_domino_cellConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_leafremoval.lean)
-/
@[path]
private lemma jc_domino_cellConnected_eq :
-- imply
  CellConnected jc_domino := by
-- proof
  apply StatMech.Walls.jc_domino_cellConnected

/--
[jc_domino_pendant_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_leafremoval.lean)
-/
@[path]
private lemma jc_domino_pendant_origin_eq :
-- imply
  jc_IsPendantCell jc_domino ![0, 0] := by
-- proof
  apply StatMech.Walls.jc_domino_pendant_origin

/--
[jc_domino_leaf_removal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_leafremoval.lean)
-/
@[path]
private lemma jc_domino_leaf_removal_eq :
-- imply
  CellConnected (jc_domino \ {![0, 0]}) := by
-- proof
  apply StatMech.Walls.jc_domino_leaf_removal


-- created on 2026-10-23
