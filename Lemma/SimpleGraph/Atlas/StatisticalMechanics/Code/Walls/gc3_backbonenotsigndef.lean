import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc3_backbonenotsigndef
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc3_backbone_not_signDefinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_backbonenotsigndef.lean)
-/
@[path]
private lemma gc3_backbone_not_signDefinite_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m₁ m₂ : Finset ι}
  {o x y : V}
-- given
  (h₁ : aie_allConn ends m₁ o x y)
  (h₂ : aie_noneConn ends m₂ o x y) :
-- imply
  asd_ghsBackboneFactor ends m₁ o x y < 0 ∧ 0 < asd_ghsBackboneFactor ends m₂ o x y := by
-- proof
  apply StatMech.Walls.gc3_backbone_not_signDefinite ends m₁ m₂ h₁ h₂

/--
[gc3_qFactor_not_signDefinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_backbonenotsigndef.lean)
-/
@[path]
private lemma gc3_qFactor_not_signDefinite_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hxy : x ≠ y) :
-- imply
  (∃ q : ConfigSpace V, ghsQFactor q o x y < 0) ∧ (∃ q : ConfigSpace V, 0 < ghsQFactor q o x y) := by
-- proof
  apply StatMech.Walls.gc3_qFactor_not_signDefinite hox hxy

/--
[gc3_only_negative_cell_is_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_backbonenotsigndef.lean)
-/
@[path]
private lemma gc3_only_negative_cell_is_allConn_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (hneg : asd_ghsBackboneFactor ends m o x y < 0) :
-- imply
  aie_allConn ends m o x y := by
-- proof
  apply StatMech.Walls.gc3_only_negative_cell_is_allConn ends m o x y hneg

/--
[gc3_not_termwise_signDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_backbonenotsigndef.lean)
-/
@[path]
private lemma gc3_not_termwise_signDominance_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m₁ m₂ : Finset ι}
  {o x y : V}
-- given
  (h₁ : aie_allConn ends m₁ o x y)
  (h₂ : aie_noneConn ends m₂ o x y) :
-- imply
  (¬ ∀ m : Finset ι, asd_ghsBackboneFactor ends m o x y ≤ 0) ∧ (¬ ∀ m : Finset ι, 0 ≤ asd_ghsBackboneFactor ends m o x y) := by
-- proof
  apply StatMech.Walls.gc3_not_termwise_signDominance ends m₁ m₂ h₁ h₂

/--
[gc3_connK_empty_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_backbonenotsigndef.lean)
-/
@[path]
private lemma gc3_connK_empty_eq_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {a b : V}
-- given
  (h : connK ends (∅ : Finset ι) a b) :
-- imply
  a = b := by
-- proof
  apply StatMech.Walls.gc3_connK_empty_eq ends h

/--
[gc3_noneConn_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_backbonenotsigndef.lean)
-/
@[path]
private lemma gc3_noneConn_empty_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  aie_noneConn ends (∅ : Finset ι) o x y := by
-- proof
  apply StatMech.Walls.gc3_noneConn_empty ends hox hoy hxy

/--
[gc3_allConn_concrete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_backbonenotsigndef.lean)
-/
@[path]
private lemma gc3_allConn_concrete_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  aie_allConn (fun i : Fin 2 => if i = 0 then s((0 : Fin 3), 1) else s((1 : Fin 3), 2)) ({0, 1} : Finset (Fin 2)) 0 1 2 := by
-- proof
  apply StatMech.Walls.gc3_allConn_concrete

/--
[gc3_backbone_not_signDefinite_concrete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_backbonenotsigndef.lean)
-/
@[path]
private lemma gc3_backbone_not_signDefinite_concrete_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  asd_ghsBackboneFactor (fun i : Fin 2 => if i = 0 then s((0 : Fin 3), 1) else s((1 : Fin 3), 2)) ({0, 1} : Finset (Fin 2)) 0 1 2 < 0 ∧ 0 < asd_ghsBackboneFactor (fun i : Fin 2 => if i = 0 then s((0 : Fin 3), 1) else s((1 : Fin 3), 2)) (∅ : Finset (Fin 2)) 0 1 2 := by
-- proof
  apply StatMech.Walls.gc3_backbone_not_signDefinite_concrete

/--
[gc3_obstruction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_backbonenotsigndef.lean)
-/
@[path]
private lemma gc3_obstruction_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m₁ m₂ : Finset ι}
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hxy : x ≠ y)
  (h₁ : aie_allConn ends m₁ o x y)
  (h₂ : aie_noneConn ends m₂ o x y) :
-- imply
  (asd_ghsBackboneFactor ends m₁ o x y = -2 ∧ asd_ghsBackboneFactor ends m₂ o x y = 1) ∧ (asd_ghsBackboneFactor ends m₁ o x y < 0 ∧ 0 < asd_ghsBackboneFactor ends m₂ o x y) ∧ (ghsQFactor (V := V) (fun _ => true) o x y = -2 ∧ ghsQFactor (V := V) (fun z => decide (z ≠ x)) o x y = 2) ∧ ((∃ q : ConfigSpace V, ghsQFactor q o x y < 0) ∧ (∃ q : ConfigSpace V, 0 < ghsQFactor q o x y)) := by
-- proof
  apply StatMech.Walls.gc3_obstruction ends m₁ m₂ hox hxy h₁ h₂


-- created on 2026-10-23
