import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc29hdom
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc29_allConnMass_le_partitionFunction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc29hdom.lean)
-/
@[path]
private lemma gc29_allConnMass_le_partitionFunction_eq
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
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B) ≤ ∑ m ∈ M, hnw_mass G β J m B := by
-- proof
  apply StatMech.Walls.gc29_allConnMass_le_partitionFunction G β J hβ hJ M B o x y

/--
[gc29_allConn_prob_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc29hdom.lean)
-/
@[path]
private lemma gc29_allConn_prob_le_one_eq
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
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  tcp_allConnProb G β J M B o x y ≤ 1 := by
-- proof
  apply StatMech.Walls.gc29_allConn_prob_le_one G β J hβ hJ M B o x y

/--
[gc29_allConnMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc29hdom.lean)
-/
@[path]
private lemma gc29_allConnMass_nonneg_eq
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
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B := by
-- proof
  apply StatMech.Walls.gc29_allConnMass_nonneg G β J hβ hJ M B o x y

/--
[gc29_hdom_iff_full_gap_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc29hdom.lean)
-/
@[path]
private lemma gc29_hdom_iff_full_gap_nonneg_eq
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
  (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hm : ∀ m ∈ M, Sharpness.sources G m = B)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hcoh : ∀ m ∈ M, hnw_coherent G m o x y) :
-- imply
  (2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B) ≤ ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m B) ↔ 0 ≤ ∑ m ∈ M, hnw_gap G β J m B o x y := by
-- proof
  apply StatMech.Walls.gc29_hdom_iff_full_gap_nonneg G β J M hnd B hm hox hoy hxy hcoh

/--
[gc29_full_gap_can_be_negative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc29hdom.lean)
-/
@[path]
private lemma gc29_full_gap_can_be_negative_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ∑ m ∈ ({hmu_triM} : Finset (Sharpness.Current (Fin 3))), hnw_gap hmu_TriG 1 (fun _ => 1) m ∅ 0 1 2 < 0 := by
-- proof
  apply StatMech.Walls.gc29_full_gap_can_be_negative G

/--
[gc29_triangle_probLeOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc29hdom.lean)
-/
@[path]
private lemma gc29_triangle_probLeOne_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  (∑ m ∈ ({hmu_triM} : Finset (Sharpness.Current (Fin 3))).filter (fun m => hnw_allConn hmu_TriG m 0 1 2), hnw_mass hmu_TriG 1 (fun _ => 1) m ∅) ≤ ∑ m ∈ ({hmu_triM} : Finset (Sharpness.Current (Fin 3))), hnw_mass hmu_TriG 1 (fun _ => 1) m ∅ := by
-- proof
  apply StatMech.Walls.gc29_triangle_probLeOne G

/--
[gc29_probLeOne_does_not_give_hdom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc29hdom.lean)
-/
@[path]
private lemma gc29_probLeOne_does_not_give_hdom_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ((∑ m ∈ ({hmu_triM} : Finset (Sharpness.Current (Fin 3))).filter (fun m => hnw_allConn hmu_TriG m 0 1 2), hnw_mass hmu_TriG 1 (fun _ => 1) m ∅) ≤ ∑ m ∈ ({hmu_triM} : Finset (Sharpness.Current (Fin 3))), hnw_mass hmu_TriG 1 (fun _ => 1) m ∅) ∧ ¬ (2 * (∑ m ∈ ({hmu_triM} : Finset (Sharpness.Current (Fin 3))).filter (fun m => hnw_allConn hmu_TriG m 0 1 2), hnw_mass hmu_TriG 1 (fun _ => 1) m ∅) ≤ ∑ m ∈ ({hmu_triM} : Finset (Sharpness.Current (Fin 3))).filter (fun m => hnw_noneConn hmu_TriG m 0 1 2), hnw_mass hmu_TriG 1 (fun _ => 1) m ∅) := by
-- proof
  apply StatMech.Walls.gc29_probLeOne_does_not_give_hdom G

/--
[gc29_allConn_summed_gap_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc29hdom.lean)
-/
@[path]
private lemma gc29_allConn_summed_gap_eq_eq
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
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_gap G β J m B o x y = -2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B) := by
-- proof
  apply StatMech.Walls.gc29_allConn_summed_gap_eq G β J M B hox hoy hxy

/--
[gc29_full_gap_eq_allConn_gap_add_noneMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc29hdom.lean)
-/
@[path]
private lemma gc29_full_gap_eq_allConn_gap_add_noneMass_eq
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
  (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hm : ∀ m ∈ M, Sharpness.sources G m = B)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hcoh : ∀ m ∈ M, hnw_coherent G m o x y) :
-- imply
  ∑ m ∈ M, hnw_gap G β J m B o x y = (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_gap G β J m B o x y) + ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m B := by
-- proof
  apply StatMech.Walls.gc29_full_gap_eq_allConn_gap_add_noneMass G β J M hnd B hm hox hoy hxy hcoh

/--
[gc29_hdom_of_backboneReroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc29hdom.lean)
-/
@[path]
private lemma gc29_hdom_of_backboneReroute_eq
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
  (hres : gc29_BackboneReroute G β J M B o x y) :
-- imply
  2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B) ≤ ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m B := by
-- proof
  apply StatMech.Walls.gc29_hdom_of_backboneReroute G β J M B hres

/--
[gc29_backboneReroute_of_hdom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc29hdom.lean)
-/
@[path]
private lemma gc29_backboneReroute_of_hdom_eq
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
  (hdom : 2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B) ≤ ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m B) :
-- imply
  gc29_BackboneReroute G β J M B o x y := by
-- proof
  apply StatMech.Walls.gc29_backboneReroute_of_hdom G β J hβ hJ M B hdom

/--
[gc29_native_gap_nonneg_of_backboneReroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc29hdom.lean)
-/
@[path]
private lemma gc29_native_gap_nonneg_of_backboneReroute_eq
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
  (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hm : ∀ m ∈ M, Sharpness.sources G m = B)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hcoh : ∀ m ∈ M, hnw_coherent G m o x y)
  (hres : gc29_BackboneReroute G β J M B o x y) :
-- imply
  0 ≤ ∑ m ∈ M, hnw_gap G β J m B o x y := by
-- proof
  apply StatMech.Walls.gc29_native_gap_nonneg_of_backboneReroute G β J M hnd B hm hox hoy hxy hcoh hres

/--
[gc29_backboneReroute_of_allConnMass_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc29hdom.lean)
-/
@[path]
private lemma gc29_backboneReroute_of_allConnMass_zero_eq
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
  (hzero : (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B) = 0) :
-- imply
  gc29_BackboneReroute G β J M B o x y := by
-- proof
  apply StatMech.Walls.gc29_backboneReroute_of_allConnMass_zero G β J hβ hJ M B hzero


-- created on 2026-10-23
