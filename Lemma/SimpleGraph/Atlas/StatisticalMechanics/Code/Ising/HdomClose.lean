import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.HdomClose
open Finset Classical StatMech StatMech.Ising


/--
[hdc_signSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomClose.lean)
-/
@[path]
private lemma hdc_signSwap_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {A : Finset V}
  {u v : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hm : Sharpness.sources G m = A)
  (huv : u ≠ v)
  (hconn : connP (oddEdges G.edgeFinset m) u v ∨ ¬ connP (posEdges G.edgeFinset m) u v) :
-- imply
  hnw_mass G β J m (A ∆ {u, v}) ≤ hnw_mass G β J m A := by
-- proof
  apply StatMech.Ising.hdc_signSwap G β J hβ hJ m hnd A hm huv hconn

/--
[hdc_reroute_eq_base_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomClose.lean)
-/
@[path]
private lemma hdc_reroute_eq_base_allConn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {A : Finset V}
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hall : hnw_allConn G m o x y) :
-- imply
  hnw_mass G β J m (A ∆ {x, y}) = hnw_mass G β J m A ∧ hnw_mass G β J m (A ∆ {o, y}) = hnw_mass G β J m A ∧ hnw_mass G β J m (A ∆ {o, x}) = hnw_mass G β J m A := by
-- proof
  apply StatMech.Ising.hdc_reroute_eq_base_allConn G β J m A hox hoy hxy hall

/--
[hdc_allConn_self_domination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomClose.lean)
-/
@[path]
private lemma hdc_allConn_self_domination_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {A : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A) ≤ ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), (hnw_mass G β J m (A ∆ {x, y}) + hnw_mass G β J m (A ∆ {o, y}) + hnw_mass G β J m (A ∆ {o, x})) := by
-- proof
  apply StatMech.Ising.hdc_allConn_self_domination G β J hβ hJ M A hox hoy hxy

/--
[hdc_allConn_gap_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomClose.lean)
-/
@[path]
private lemma hdc_allConn_gap_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {A : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hall : hnw_allConn G m o x y) :
-- imply
  hnw_gap G β J m A o x y ≤ 0 := by
-- proof
  apply StatMech.Ising.hdc_allConn_gap_nonpos G β J hβ hJ m A hox hoy hxy hall

/--
[hdc_allConn_summed_gap_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomClose.lean)
-/
@[path]
private lemma hdc_allConn_summed_gap_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {A : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_gap G β J m A o x y ≤ 0 := by
-- proof
  apply StatMech.Ising.hdc_allConn_summed_gap_nonpos G β J hβ hJ M A hox hoy hxy

/--
[hdc_allConn_mass_le_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomClose.lean)
-/
@[path]
private lemma hdc_allConn_mass_le_full_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {A : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A ≤ ∑ m ∈ M, hnw_mass G β J m A := by
-- proof
  apply StatMech.Ising.hdc_allConn_mass_le_full G β J hβ hJ M A

/--
[hdc_pairwise_full_dom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomClose.lean)
-/
@[path]
private lemma hdc_pairwise_full_dom_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {A : Finset V}
  {u v : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hm : ∀ m ∈ M, Sharpness.sources G m = A)
  (huv : u ≠ v)
  (hcoh : ∀ m ∈ M, connP (oddEdges G.edgeFinset m) u v ↔ connP (posEdges G.edgeFinset m) u v) :
-- imply
  ∑ m ∈ M, hnw_mass G β J m (A ∆ {u, v}) ≤ ∑ m ∈ M, hnw_mass G β J m A := by
-- proof
  apply StatMech.Ising.hdc_pairwise_full_dom G β J hβ hJ M hnd A hm huv hcoh

/--
[hdc_ghs_singlePair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomClose.lean)
-/
@[path]
private lemma hdc_ghs_singlePair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {A : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hm : ∀ m ∈ M, Sharpness.sources G m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hcoh : ∀ m ∈ M, hnw_coherent G m o x y) :
-- imply
  (∑ m ∈ M, hnw_mass G β J m (A ∆ {x, y}) ≤ ∑ m ∈ M, hnw_mass G β J m A) ∧ (∑ m ∈ M, hnw_mass G β J m (A ∆ {o, y}) ≤ ∑ m ∈ M, hnw_mass G β J m A) ∧ (∑ m ∈ M, hnw_mass G β J m (A ∆ {o, x}) ≤ ∑ m ∈ M, hnw_mass G β J m A) := by
-- proof
  apply StatMech.Ising.hdc_ghs_singlePair G β J hβ hJ M hnd A hm hox hoy hxy hcoh

/--
[hdc_hdom_cross_class_refutable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomClose.lean)
-/
@[path]
private lemma hdc_hdom_cross_class_refutable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ¬ (2 * (∑ m ∈ ({hmu_triM} : Finset (Current (Fin 3))).filter (fun m => hnw_allConn hmu_TriG m 0 1 2), hnw_mass hmu_TriG 1 (fun _ => 1) m ∅) ≤ ∑ m ∈ ({hmu_triM} : Finset (Current (Fin 3))).filter (fun m => hnw_noneConn hmu_TriG m 0 1 2), hnw_mass hmu_TriG 1 (fun _ => 1) m ∅) := by
-- proof
  apply StatMech.Ising.hdc_hdom_cross_class_refutable G

/--
[hdc_ghs_distinct_site_of_hdom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomClose.lean)
-/
@[path]
private lemma hdc_ghs_distinct_site_of_hdom_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {A : Finset V}
  {o x y : V}
-- given
  (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hm : ∀ m ∈ M, Sharpness.sources G m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hcoh : ∀ m ∈ M, hnw_coherent G m o x y)
  (hdom : 2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A) ≤ ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m A) :
-- imply
  (∑ m ∈ M, hnw_mass G β J m (A ∆ {x, y})) + (∑ m ∈ M, hnw_mass G β J m (A ∆ {o, y})) + (∑ m ∈ M, hnw_mass G β J m (A ∆ {o, x})) ≤ ∑ m ∈ M, hnw_mass G β J m A := by
-- proof
  apply StatMech.Ising.hdc_ghs_distinct_site_of_hdom G β J M hnd A hm hox hoy hxy hcoh hdom


-- created on 2026-10-23
