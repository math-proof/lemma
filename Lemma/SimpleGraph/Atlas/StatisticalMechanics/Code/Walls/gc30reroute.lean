import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc30reroute
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc30_reroute_false_at_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc30reroute.lean)
-/
@[path]
private lemma gc30_reroute_false_at_general_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ¬ gc29_BackboneReroute hmu_TriG 1 (fun _ => 1) {hmu_triM} ∅ 0 1 2 := by
-- proof
  apply StatMech.Walls.gc30_reroute_false_at_general G

/--
[gc30_backbone_for_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc30reroute.lean)
-/
@[path]
private lemma gc30_backbone_for_allConn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Sharpness.Current V}
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hall : hnw_allConn G m o x y) :
-- imply
  ∃ P ⊆ oddEdges G.edgeFinset m, srcP P = ({x, y} : Finset V) ∧ (∀ e ∈ P, Odd (m e)) ∧ Disjoint (oddEdges G.edgeFinset (hmu_addBackbone P m)) P := by
-- proof
  apply StatMech.Walls.gc30_backbone_for_allConn G m hox hoy hxy hall

/--
[gc30_addBackbone_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc30reroute.lean)
-/
@[path]
private lemma gc30_addBackbone_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Sharpness.Current V}
  {P : Finset (Sym2 V)}
-- given
  (hP : P ⊆ G.edgeFinset)
  (hPsrc : srcP P = ({x, y} : Finset V)) :
-- imply
  Sharpness.sources G (hmu_addBackbone P m) = Sharpness.sources G m ∆ ({x, y} : Finset V) := by
-- proof
  apply StatMech.Walls.gc30_addBackbone_sources G m P hP hPsrc

/--
[gc30_addBackbone_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc30reroute.lean)
-/
@[path]
private lemma gc30_addBackbone_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {P : Finset (Sym2 V)} :
-- imply
  Function.Injective (hmu_addBackbone (V := V) P) := by
-- proof
  apply StatMech.Walls.gc30_addBackbone_injective G P

/--
[gc30_surgery_posDisconnect_obstruction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc30reroute.lean)
-/
@[path]
private lemma gc30_surgery_posDisconnect_obstruction_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Sharpness.Current V}
  {P : Finset (Sym2 V)}
  {u v : V}
-- given
  (h : connP (posEdges G.edgeFinset m) u v) :
-- imply
  connP (posEdges G.edgeFinset (hmu_addBackbone P m)) u v := by
-- proof
  apply StatMech.Walls.gc30_surgery_posDisconnect_obstruction G m P h

/--
[gc30_surgery_not_noneConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc30reroute.lean)
-/
@[path]
private lemma gc30_surgery_not_noneConn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Sharpness.Current V}
  {P : Finset (Sym2 V)}
  {o x y : V}
-- given
  (hall : hnw_allConn G m o x y) :
-- imply
  ¬ hnw_noneConn G (hmu_addBackbone P m) o x y := by
-- proof
  apply StatMech.Walls.gc30_surgery_not_noneConn G m P hall

/--
[gc30_reroute_of_backboneSurgery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc30reroute.lean)
-/
@[path]
private lemma gc30_reroute_of_backboneSurgery_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Sharpness.Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hsurg : bbr_BackboneSurgery G β J M B o x y) :
-- imply
  gc29_BackboneReroute G β J M B o x y := by
-- proof
  apply StatMech.Walls.gc30_reroute_of_backboneSurgery G β J hβ hJ M B o x y hsurg

/--
[gc30_native_gap_nonneg_of_backboneSurgery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc30reroute.lean)
-/
@[path]
private lemma gc30_native_gap_nonneg_of_backboneSurgery_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Sharpness.Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hm : ∀ m ∈ M, Sharpness.sources G m = B)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hcoh : ∀ m ∈ M, hnw_coherent G m o x y)
  (hsurg : bbr_BackboneSurgery G β J M B o x y) :
-- imply
  0 ≤ ∑ m ∈ M, hnw_gap G β J m B o x y := by
-- proof
  apply StatMech.Walls.gc30_native_gap_nonneg_of_backboneSurgery G β J hβ hJ M hnd B hm hox hoy hxy hcoh hsurg

/--
[gc30_backboneSurgery_of_allConn_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc30reroute.lean)
-/
@[path]
private lemma gc30_backboneSurgery_of_allConn_free_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Sharpness.Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hno : bbr_allFilter G M o x y = ∅) :
-- imply
  bbr_BackboneSurgery G β J M B o x y := by
-- proof
  apply StatMech.Walls.gc30_backboneSurgery_of_allConn_free G β J M B o x y hno

/--
[gc30_reroute_of_allConn_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc30reroute.lean)
-/
@[path]
private lemma gc30_reroute_of_allConn_free_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Sharpness.Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hno : bbr_allFilter G M o x y = ∅) :
-- imply
  gc29_BackboneReroute G β J M B o x y := by
-- proof
  apply StatMech.Walls.gc30_reroute_of_allConn_free G β J hβ hJ M B o x y hno


-- created on 2026-10-23
