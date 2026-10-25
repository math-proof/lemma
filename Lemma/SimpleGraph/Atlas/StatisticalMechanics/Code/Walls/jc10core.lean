import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc10core.Part4
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[jc10core_countP_or_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10core.lean)
-/
@[path]
private lemma jc10core_countP_or_decomp_eq
  {l : List α}
  [DecidablePred p]
  [DecidablePred q]
  [DecidablePred r]
-- given
  (p q r : α → Prop)
  (hdec : ∀ a, p a ↔ (q a ∨ r a))
  (hexcl : ∀ a, ¬ (q a ∧ r a)) :
-- imply
  l.countP (fun a => decide (p a)) = l.countP (fun a => decide (q a)) + l.countP (fun a => decide (r a)) := by
-- proof
  apply StatMech.Walls.jc10core_countP_or_decomp l p q r hdec hexcl

/--
[jc10core_dartFace_row_le_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10core.lean)
-/
@[path]
private lemma jc10core_dartFace_row_le_tail_eq
  {e : Dart} :
-- imply
  (dartFace e) 1 ≤ e.tail 1 := by
-- proof
  apply StatMech.Walls.jc10core_dartFace_row_le_tail e

/--
[jc10core_support_row_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10core.lean)
-/
@[path]
private lemma jc10core_support_row_le_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {c : Site 2}
  {p : Site 2}
-- given
  (hc : IsExtremeCell K c)
  (hp : p ∈ (mpl_orbitLoop K a).support) :
-- imply
  p 1 ≤ c 1 := by
-- proof
  apply StatMech.Walls.jc10core_support_row_le K a c hc p hp

/--
[jc10core_colPt_off_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10core.lean)
-/
@[path]
private lemma jc10core_colPt_off_support_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {c : Site 2}
  {j : ℤ}
-- given
  (hc : IsExtremeCell K c)
  (hj : c 1 < j) :
-- imply
  (![c 0, j] : Site 2) ∉ (mpl_orbitLoop K a).support := by
-- proof
  apply StatMech.Walls.jc10core_colPt_off_support K a c hc j hj

/--
[jc10core_col_parity_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10core.lean)
-/
@[path]
private lemma jc10core_col_parity_const_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {c : Site 2}
  {n : ℕ}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  (Even (jec_rayCount (![c 0, c 1 + 1 + (n : ℤ)] : Site 2) (mpl_orbitLoop K a)) ↔ Even (jec_rayCount (![c 0, c 1 + 1] : Site 2) (mpl_orbitLoop K a))) := by
-- proof
  apply StatMech.Walls.jc10core_col_parity_const K a c hc n

/--
[jc10core_above_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10core.lean)
-/
@[path]
private lemma jc10core_above_even_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  Even (jec_rayCount (![c 0, c 1 + 1] : Site 2) (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Walls.jc10core_above_even K a c hc

/--
[jc10core_topWallEdge_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10core.lean)
-/
@[path]
private lemma jc10core_topWallEdge_mk_eq
  {c x y : Site 2} :
-- imply
  jc10core_topWallEdge c s(x, y) ↔ (x 1 = y 1 ∧ x 1 = c 1) ∧ ((x 0 = c 0 - 1 ∧ y 0 = c 0) ∨ (y 0 = c 0 - 1 ∧ x 0 = c 0)) := by
-- proof
  apply StatMech.Walls.jc10core_topWallEdge_mk c x y

/--
[jc10core_wallEdge_up_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10core.lean)
-/
@[path]
private lemma jc10core_wallEdge_up_decomp_eq
  {c x y : Site 2} :
-- imply
  jec_wallEdge (![c 0, c 1 + 1] : Site 2) s(x, y) ↔ (jec_wallEdge c s(x, y) ∨ jc10core_topWallEdge c s(x, y)) := by
-- proof
  apply StatMech.Walls.jc10core_wallEdge_up_decomp c x y

/--
[jc10core_wallEdge_topWall_excl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10core.lean)
-/
@[path]
private lemma jc10core_wallEdge_topWall_excl_eq
  {c x y : Site 2} :
-- imply
  ¬ (jec_wallEdge c s(x, y) ∧ jc10core_topWallEdge c s(x, y)) := by
-- proof
  apply StatMech.Walls.jc10core_wallEdge_topWall_excl c x y

/--
[jc10core_wallCount_up](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10core.lean)
-/
@[path]
private lemma jc10core_wallCount_up_eq
  {c : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y} :
-- imply
  jec_wallCount (![c 0, c 1 + 1] : Site 2) w = jec_wallCount c w + jc10core_topWallCount c w := by
-- proof
  apply StatMech.Walls.jc10core_wallCount_up c w

/--
[jc10core_cornerCellOdd_of_topWallOdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10core.lean)
-/
@[path]
private lemma jc10core_cornerCellOdd_of_topWallOdd_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c)
  (htop : ¬ Even (jc10core_topWallCount c (mpl_orbitLoop K a))) :
-- imply
  ¬ Even (jec_rayCount c (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Walls.jc10core_cornerCellOdd_of_topWallOdd K a c hc htop

/--
[jc10core_windingWitness_of_topWallOdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10core.lean)
-/
@[path]
private lemma jc10core_windingWitness_of_topWallOdd_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c)
  (htop : ¬ Even (jc10core_topWallCount c (mpl_orbitLoop K a))) :
-- imply
  ∃ z₀ : Site 2, z₀ ∈ K ∧ ¬ Even (jec_rayCount z₀ (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Walls.jc10core_windingWitness_of_topWallOdd K a c hc htop

/--
[jc10core_cornerCellOdd_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10core.lean)
-/
@[path]
private lemma jc10core_cornerCellOdd_of_residue_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c)
  (hres : jc10core_TopWallOdd K a c) :
-- imply
  ¬ Even (jec_rayCount c (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Walls.jc10core_cornerCellOdd_of_residue K a c hc hres

/--
[jc10core_exists_windingWitness_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10core.lean)
-/
@[path]
private lemma jc10core_exists_windingWitness_of_residue_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty)
  (hres : ∀ c : Site 2, ∀ hc : IsExtremeCell K c, jc10core_TopWallOdd K (extremeBase K c hc) c) :
-- imply
  ∃ c : Site 2, ∀ hc : IsExtremeCell K c, c ∈ K ∧ ¬ Even (jec_rayCount c (mpl_orbitLoop K (extremeBase K c hc))) := by
-- proof
  apply StatMech.Walls.jc10core_exists_windingWitness_of_residue K hK hne hres

/--
[jc10core_unitCell_topWallCount_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10core.lean)
-/
@[path]
private lemma jc10core_unitCell_topWallCount_eq_one_eq :
-- imply
  jc10core_topWallCount (![0, 0] : Site 2) (mpl_orbitLoop unitCell ucBase) = 1 := by
-- proof
  apply StatMech.Walls.jc10core_unitCell_topWallCount_eq_one

/--
[jc10core_unitCell_topWall_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10core.lean)
-/
@[path]
private lemma jc10core_unitCell_topWall_odd_eq :
-- imply
  jc10core_TopWallOdd unitCell ucBase (![0, 0] : Site 2) := by
-- proof
  apply StatMech.Walls.jc10core_unitCell_topWall_odd

/--
[jc10core_unitCell_cornerCellOdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10core.lean)
-/
@[path]
private lemma jc10core_unitCell_cornerCellOdd_eq :
-- imply
  ¬ Even (jec_rayCount (![0, 0] : Site 2) (mpl_orbitLoop unitCell ucBase)) := by
-- proof
  apply StatMech.Walls.jc10core_unitCell_cornerCellOdd


-- created on 2026-10-23
