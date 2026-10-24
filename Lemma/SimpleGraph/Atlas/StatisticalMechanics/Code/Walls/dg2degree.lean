import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.dg2degree
open Finset Set SimpleGraph StatMech StatMech.Walls


/--
[dg2_degree_eq_transitions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dg2degree.lean)
-/
@[path]
private lemma dg2_degree_eq_transitions_eq
  {K : Set (Site 2)}
  {a b : ℤ} :
-- imply
  (faceBoundaryGraph K).degree ![a, b] = faceBoundaryDegree K a b := by
-- proof
  apply StatMech.Walls.dg2_degree_eq_transitions K a b

/--
[dg2_bdInd_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dg2degree.lean)
-/
@[path]
private lemma dg2_bdInd_eq_eq
  {K : Set (Site 2)}
  {x y : Site 2} :
-- imply
  bdInd K x y = if (x ∈ K ↔ y ∉ K) then 1 else 0 := by
-- proof
  apply StatMech.Walls.dg2_bdInd_eq K x y

/--
[dg2_degree_eq_four_iff_checker](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dg2degree.lean)
-/
@[path]
private lemma dg2_degree_eq_four_iff_checker_eq
  {K : Set (Site 2)}
  {a b : ℤ} :
-- imply
  (faceBoundaryGraph K).degree ![a, b] = 4 ↔ dg2_Checker K a b := by
-- proof
  apply StatMech.Walls.dg2_degree_eq_four_iff_checker K a b

/--
[dg2_degree_eq_zero_iff_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dg2degree.lean)
-/
@[path]
private lemma dg2_degree_eq_zero_iff_uniform_eq
  {K : Set (Site 2)}
  {a b : ℤ} :
-- imply
  (faceBoundaryGraph K).degree ![a, b] = 0 ↔ ((![a, b] : Site 2) ∈ K ↔ (![a + 1, b] : Site 2) ∈ K) ∧ ((![a + 1, b] : Site 2) ∈ K ↔ (![a + 1, b + 1] : Site 2) ∈ K) ∧ ((![a + 1, b + 1] : Site 2) ∈ K ↔ (![a, b + 1] : Site 2) ∈ K) := by
-- proof
  apply StatMech.Walls.dg2_degree_eq_zero_iff_uniform K a b

/--
[dg2_degree_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dg2degree.lean)
-/
@[path]
private lemma dg2_degree_le_two_eq
  {K : Set (Site 2)}
  {f : Site 2}
-- given
  (hK : dg2_NoPinch K) :
-- imply
  (faceBoundaryGraph K).degree f ≤ 2 := by
-- proof
  apply StatMech.Walls.dg2_degree_le_two hK f

/--
[dg2_degree_pos_of_mem_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dg2degree.lean)
-/
@[path]
private lemma dg2_degree_pos_of_mem_support_eq
  {K : Set (Site 2)}
  {f : Site 2}
-- given
  (hf : f ∈ (faceBoundaryGraph K).support) :
-- imply
  1 ≤ (faceBoundaryGraph K).degree f := by
-- proof
  apply StatMech.Walls.dg2_degree_pos_of_mem_support hf

/--
[dg2_boundary_degree_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dg2degree.lean)
-/
@[path]
private lemma dg2_boundary_degree_eq_two_eq
  {K : Set (Site 2)}
  {f : Site 2}
-- given
  (hK : dg2_NoPinch K)
  (hf : f ∈ (faceBoundaryGraph K).support) :
-- imply
  (faceBoundaryGraph K).degree f = 2 := by
-- proof
  apply StatMech.Walls.dg2_boundary_degree_eq_two hK hf

/--
[dg2_mem_pinchSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dg2degree.lean)
-/
@[path]
private lemma dg2_mem_pinchSet_eq
  {p q : ℤ} :
-- imply
  (![p, q] : Site 2) ∈ dg2_pinchSet ↔ (p = 0 ∧ q = 0) ∨ (p = 1 ∧ q = 1) := by
-- proof
  apply StatMech.Walls.dg2_mem_pinchSet p q

/--
[dg2_pinch_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dg2degree.lean)
-/
@[path]
private lemma dg2_pinch_witness_eq :
-- imply
  (faceBoundaryGraph dg2_pinchSet).degree ![(0:ℤ), 0] = 4 := by
-- proof
  apply StatMech.Walls.dg2_pinch_witness

/--
[dg2_pinchSet_not_noPinch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dg2degree.lean)
-/
@[path]
private lemma dg2_pinchSet_not_noPinch_eq :
-- imply
  ¬ dg2_NoPinch dg2_pinchSet := by
-- proof
  apply StatMech.Walls.dg2_pinchSet_not_noPinch

/--
[dg2_pinch_bridges_out](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dg2degree.lean)
-/
@[path]
private lemma dg2_pinch_bridges_out_eq :
-- imply
  (![(1:ℤ), 0] : Site 2) ∉ dg2_pinchSet ∧ (![(0:ℤ), 1] : Site 2) ∉ dg2_pinchSet := by
-- proof
  apply StatMech.Walls.dg2_pinch_bridges_out

/--
[dg2_tromino_noPinch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dg2degree.lean)
-/
@[path]
private lemma dg2_tromino_noPinch_eq :
-- imply
  dg2_NoPinch (↑pc2_tromino : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.dg2_tromino_noPinch

/--
[dg2_tromino_corner_degree_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dg2degree.lean)
-/
@[path]
private lemma dg2_tromino_corner_degree_eq_two_eq :
-- imply
  (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).degree ![(-1:ℤ), -1] = 2 := by
-- proof
  apply StatMech.Walls.dg2_tromino_corner_degree_eq_two

/--
[dg2_boxPred_noPinch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dg2degree.lean)
-/
@[path]
private lemma dg2_boxPred_noPinch_eq
  {x0 x1 y0 y1 : ℤ} :
-- imply
  dg2_NoPinch {p : Site 2 | x0 ≤ p 0 ∧ p 0 ≤ x1 ∧ y0 ≤ p 1 ∧ p 1 ≤ y1} := by
-- proof
  apply StatMech.Walls.dg2_boxPred_noPinch x0 x1 y0 y1

/--
[dg2_checker_iff_diagSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dg2degree.lean)
-/
@[path]
private lemma dg2_checker_iff_diagSplit_eq
  {K : Set (Site 2)}
  {a b : ℤ} :
-- imply
  dg2_Checker K a b ↔ ((![a, b] : Site 2) ∈ K ∧ (![a + 1, b + 1] : Site 2) ∈ K ∧ (![a + 1, b] : Site 2) ∉ K ∧ (![a, b + 1] : Site 2) ∉ K) ∨ ((![a, b] : Site 2) ∉ K ∧ (![a + 1, b + 1] : Site 2) ∉ K ∧ (![a + 1, b] : Site 2) ∈ K ∧ (![a, b + 1] : Site 2) ∈ K) := by
-- proof
  apply StatMech.Walls.dg2_checker_iff_diagSplit K a b

/--
[dg2_boundary_degree_eq_two_of_bothConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dg2degree.lean)
-/
@[path]
private lemma dg2_boundary_degree_eq_two_of_bothConnected_eq
  {K : Set (Site 2)}
  {f : Site 2}
-- given
  (hres : dg2_NoPinch_of_bothConnected_Statement)
  (hK : ((hypercubicLattice 2).induce K).Connected)
  (hKc : ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Connected)
  (hf : f ∈ (faceBoundaryGraph K).support) :
-- imply
  (faceBoundaryGraph K).degree f = 2 := by
-- proof
  apply StatMech.Walls.dg2_boundary_degree_eq_two_of_bothConnected hres hK hKc hf


-- created on 2026-10-23
