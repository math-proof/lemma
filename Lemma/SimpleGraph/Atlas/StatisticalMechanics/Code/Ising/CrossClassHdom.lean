import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.CrossClassHdom
open Finset Classical StatMech StatMech.Ising


/--
[cch_allConn_reroute_eq_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CrossClassHdom.lean)
-/
@[path]
private lemma cch_allConn_reroute_eq_base_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {B : Finset V}
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hall : hnw_allConn G m o x y) :
-- imply
  hnw_mass G β J m (B ∆ {x, y}) = hnw_mass G β J m B ∧ hnw_mass G β J m (B ∆ {o, y}) = hnw_mass G β J m B ∧ hnw_mass G β J m (B ∆ {o, x}) = hnw_mass G β J m B := by
-- proof
  apply StatMech.Ising.cch_allConn_reroute_eq_base G β J m B hox hoy hxy hall

/--
[cch_crossClass_surgery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CrossClassHdom.lean)
-/
@[path]
private lemma cch_crossClass_surgery_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B) ≤ (∑ m ∈ M, hnw_mass G β J m (B ∆ {x, y})) + (∑ m ∈ M, hnw_mass G β J m (B ∆ {o, y})) + (∑ m ∈ M, hnw_mass G β J m (B ∆ {o, x})) := by
-- proof
  apply StatMech.Ising.cch_crossClass_surgery G β J hβ hJ M B hox hoy hxy

/--
[cch_allConnMass_le_partitionFunction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CrossClassHdom.lean)
-/
@[path]
private lemma cch_allConnMass_le_partitionFunction_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  tcp_allConnMass G β J M B o x y ≤ tcp_partitionFunction G β J M B := by
-- proof
  apply StatMech.Ising.cch_allConnMass_le_partitionFunction G β J hβ hJ M B o x y

/--
[cch_crossClass_full_dom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CrossClassHdom.lean)
-/
@[path]
private lemma cch_crossClass_full_dom_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  2 * tcp_allConnMass G β J M B o x y ≤ tcp_partitionFunction G β J M B + tcp_allConnMass G β J M B o x y := by
-- proof
  apply StatMech.Ising.cch_crossClass_full_dom G β J hβ hJ M B o x y

/--
[cch_allConn_prob_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CrossClassHdom.lean)
-/
@[path]
private lemma cch_allConn_prob_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  tcp_allConnProb G β J M B o x y ≤ 1 := by
-- proof
  apply StatMech.Ising.cch_allConn_prob_le_one G β J hβ hJ M B o x y

/--
[cch_lebowitz_summed_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CrossClassHdom.lean)
-/
@[path]
private lemma cch_lebowitz_summed_gap_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_gap G β J m B o x y = -2 * tcp_allConnMass G β J M B o x y := by
-- proof
  apply StatMech.Ising.cch_lebowitz_summed_gap G β J M B hox hoy hxy

/--
[cch_lebowitz_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CrossClassHdom.lean)
-/
@[path]
private lemma cch_lebowitz_sign_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_gap G β J m B o x y ≤ 0 := by
-- proof
  apply StatMech.Ising.cch_lebowitz_sign G β J hβ hJ M B hox hoy hxy

/--
[cch_per_current_dom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CrossClassHdom.lean)
-/
@[path]
private lemma cch_per_current_dom_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {B : Finset V}
  {u v : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hm : Sharpness.sources G m = B)
  (huv : u ≠ v)
  (hconn : connP (oddEdges G.edgeFinset m) u v ∨ ¬ connP (posEdges G.edgeFinset m) u v) :
-- imply
  hnw_mass G β J m (B ∆ {u, v}) ≤ hnw_mass G β J m B := by
-- proof
  apply StatMech.Ising.cch_per_current_dom G β J hβ hJ m hnd B hm huv hconn

/--
[cch_eq_gri2_family](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CrossClassHdom.lean)
-/
@[path]
private lemma cch_eq_gri2_family_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {B : Finset V}
  {u v : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hm : ∀ m ∈ M, Sharpness.sources G m = B)
  (huv : u ≠ v)
  (hcoh : ∀ m ∈ M, connP (oddEdges G.edgeFinset m) u v ↔ connP (posEdges G.edgeFinset m) u v) :
-- imply
  ∑ m ∈ M, hnw_mass G β J m (B ∆ {u, v}) ≤ ∑ m ∈ M, hnw_mass G β J m B := by
-- proof
  apply StatMech.Ising.cch_eq_gri2_family G β J hβ hJ M hnd B hm huv hcoh

/--
[cch_lebowitz_closes_U4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CrossClassHdom.lean)
-/
@[path]
private lemma cch_lebowitz_closes_U4_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {B : Finset V}
  {o x y : V}
  {μ : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hμ : 0 ≤ μ) :
-- imply
  -2 * μ ≤ -2 * μ * tcp_allConnProb G β J M B o x y ∧ -2 * μ * tcp_allConnProb G β J M B o x y ≤ 0 := by
-- proof
  apply StatMech.Ising.cch_lebowitz_closes_U4 G β J hβ hJ M B o x y μ hμ

/--
[cch_crossClass_dom_iff_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CrossClassHdom.lean)
-/
@[path]
private lemma cch_crossClass_dom_iff_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
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
  apply StatMech.Ising.cch_crossClass_dom_iff_le G β J M hnd B hm hox hoy hxy hcoh

/--
[cch_full_gap_can_be_negative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CrossClassHdom.lean)
-/
@[path]
private lemma cch_full_gap_can_be_negative_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ∑ m ∈ ({hmu_triM} : Finset (Current (Fin 3))), hnw_gap hmu_TriG 1 (fun _ => 1) m ∅ 0 1 2 < 0 := by
-- proof
  apply StatMech.Ising.cch_full_gap_can_be_negative G

/--
[cch_hdom_cross_class_refutable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CrossClassHdom.lean)
-/
@[path]
private lemma cch_hdom_cross_class_refutable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ¬ (2 * (∑ m ∈ ({hmu_triM} : Finset (Current (Fin 3))).filter (fun m => hnw_allConn hmu_TriG m 0 1 2), hnw_mass hmu_TriG 1 (fun _ => 1) m ∅) ≤ ∑ m ∈ ({hmu_triM} : Finset (Current (Fin 3))).filter (fun m => hnw_noneConn hmu_TriG m 0 1 2), hnw_mass hmu_TriG 1 (fun _ => 1) m ∅) := by
-- proof
  apply StatMech.Ising.cch_hdom_cross_class_refutable G


-- created on 2026-10-23
