import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part3
open Finset Classical StatMech StatMech.Ising


/--
[hnw_mass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomNativeWeight.lean)
-/
@[path]
private lemma hnw_mass_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {S : Finset V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ hnw_mass G β J m S := by
-- proof
  apply StatMech.Ising.hnw_mass_nonneg G β J hβ hJ m S

/--
[hnw_noneConn_not_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomNativeWeight.lean)
-/
@[path]
private lemma hnw_noneConn_not_allConn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Current V}
  {o x y : V}
-- given
  (h : hnw_noneConn G m o x y) :
-- imply
  ¬ hnw_allConn G m o x y := by
-- proof
  apply StatMech.Ising.hnw_noneConn_not_allConn G m h

/--
[hnw_switching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomNativeWeight.lean)
-/
@[path]
private lemma hnw_switching_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {u v : V}
  {A : Finset V}
-- given
  (huv : u ≠ v)
  (hconn : connP (oddEdges G.edgeFinset m) u v) :
-- imply
  hnw_mass G β J m (A ∆ {u, v}) = hnw_mass G β J m A := by
-- proof
  apply StatMech.Ising.hnw_switching G β J m huv hconn A

/--
[hnw_mass_vanish](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomNativeWeight.lean)
-/
@[path]
private lemma hnw_mass_vanish_eq
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
  (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hm : Sharpness.sources G m = A)
  (huv : u ≠ v)
  (hdisc : ¬ connP (posEdges G.edgeFinset m) u v) :
-- imply
  hnw_mass G β J m (A ∆ {u, v}) = 0 := by
-- proof
  apply StatMech.Ising.hnw_mass_vanish G β J m hnd A hm huv hdisc

/--
[hnw_conn_trans_xy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomNativeWeight.lean)
-/
@[path]
private lemma hnw_conn_trans_xy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Current V}
  {o x y : V}
-- given
  (hoy : connP (oddEdges G.edgeFinset m) o y)
  (hox : connP (oddEdges G.edgeFinset m) o x) :
-- imply
  connP (oddEdges G.edgeFinset m) x y := by
-- proof
  apply StatMech.Ising.hnw_conn_trans_xy G m hoy hox

/--
[hnw_conn_trans_ox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomNativeWeight.lean)
-/
@[path]
private lemma hnw_conn_trans_ox_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Current V}
  {o x y : V}
-- given
  (hxy : connP (oddEdges G.edgeFinset m) x y)
  (hoy : connP (oddEdges G.edgeFinset m) o y) :
-- imply
  connP (oddEdges G.edgeFinset m) o x := by
-- proof
  apply StatMech.Ising.hnw_conn_trans_ox G m hxy hoy

/--
[hnw_conn_trans_oy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomNativeWeight.lean)
-/
@[path]
private lemma hnw_conn_trans_oy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Current V}
  {o x y : V}
-- given
  (hxy : connP (oddEdges G.edgeFinset m) x y)
  (hox : connP (oddEdges G.edgeFinset m) o x) :
-- imply
  connP (oddEdges G.edgeFinset m) o y := by
-- proof
  apply StatMech.Ising.hnw_conn_trans_oy G m hxy hox

/--
[hnw_gap_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomNativeWeight.lean)
-/
@[path]
private lemma hnw_gap_allConn_eq
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
  hnw_gap G β J m A o x y = -2 * hnw_mass G β J m A := by
-- proof
  apply StatMech.Ising.hnw_gap_allConn G β J m A hox hoy hxy hall

/--
[hnw_gap_noneConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomNativeWeight.lean)
-/
@[path]
private lemma hnw_gap_noneConn_eq
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
  (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hm : Sharpness.sources G m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hnone : hnw_noneConn G m o x y) :
-- imply
  hnw_gap G β J m A o x y = hnw_mass G β J m A := by
-- proof
  apply StatMech.Ising.hnw_gap_noneConn G β J m hnd A hm hox hoy hxy hnone

/--
[hnw_gap_exactlyOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomNativeWeight.lean)
-/
@[path]
private lemma hnw_gap_exactlyOne_eq
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
  (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hm : Sharpness.sources G m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hcoh : hnw_coherent G m o x y)
  (hnotall : ¬ hnw_allConn G m o x y)
  (hnotnone : ¬ hnw_noneConn G m o x y) :
-- imply
  hnw_gap G β J m A o x y = 0 := by
-- proof
  apply StatMech.Ising.hnw_gap_exactlyOne G β J m hnd A hm hox hoy hxy hcoh hnotall hnotnone

/--
[hnw_inclusion_exclusion_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomNativeWeight.lean)
-/
@[path]
private lemma hnw_inclusion_exclusion_decomp_eq
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
  (hcoh : ∀ m ∈ M, hnw_coherent G m o x y) :
-- imply
  ∑ m ∈ M, hnw_gap G β J m A o x y = (∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m A) - 2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A) := by
-- proof
  apply StatMech.Ising.hnw_inclusion_exclusion_decomp G β J M hnd A hm hox hoy hxy hcoh

/--
[hnw_closure_of_hdom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomNativeWeight.lean)
-/
@[path]
private lemma hnw_closure_of_hdom_eq
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
  0 ≤ ∑ m ∈ M, hnw_gap G β J m A o x y := by
-- proof
  apply StatMech.Ising.hnw_closure_of_hdom G β J M hnd A hm hox hoy hxy hcoh hdom

/--
[hnw_ghs_distinct_site_of_hdom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomNativeWeight.lean)
-/
@[path]
private lemma hnw_ghs_distinct_site_of_hdom_eq
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
  apply StatMech.Ising.hnw_ghs_distinct_site_of_hdom G β J M hnd A hm hox hoy hxy hcoh hdom

/--
[hnw_mass_eq_weight_mul_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomNativeWeight.lean)
-/
@[path]
private lemma hnw_mass_eq_weight_mul_count_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {A : Finset V} :
-- imply
  hnw_mass G β J m A = Sharpness.weight G β J m * ∑ K : {K : Current V // ∀ e, K e ≤ m e}, (if Sharpness.sources G K.1 = A then (∏ e ∈ G.edgeFinset, (Nat.choose (m e) (K.1 e) : ℝ)) else 0) := by
-- proof
  apply StatMech.Ising.hnw_mass_eq_weight_mul_count G β J m A

/--
[hnw_backbone_toggle_weight_preserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomNativeWeight.lean)
-/
@[path]
private lemma hnw_backbone_toggle_weight_preserving_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {P : Finset (Sym2 V)}
  {n : Current V}
-- given
  (hn : ∀ e, n e ≤ m e) :
-- imply
  Sharpness.weight G β J (reflect m P n) * Sharpness.weight G β J (fun e => m e - reflect m P n e) = Sharpness.weight G β J n * Sharpness.weight G β J (fun e => m e - n e) := by
-- proof
  apply StatMech.Ising.hnw_backbone_toggle_weight_preserving G β J m P hn

/--
[hnw_allMass_eq_paired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomNativeWeight.lean)
-/
@[path]
private lemma hnw_allMass_eq_paired_eq
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
  apply StatMech.Ising.hnw_allMass_eq_paired G β J m A hox hoy hxy hall

/--
[hnw_allConn_per_super_dom_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomNativeWeight.lean)
-/
@[path]
private lemma hnw_allConn_per_super_dom_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {A : Finset V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  (2 * hnw_mass G β J m A ≤ 0) ↔ hnw_mass G β J m A = 0 := by
-- proof
  apply StatMech.Ising.hnw_allConn_per_super_dom_iff G β J hβ hJ m A

/--
[hnw_sources_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomNativeWeight.lean)
-/
@[path]
private lemma hnw_sources_indicator_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {P : Finset (Sym2 V)}
-- given
  (hP : P ⊆ G.edgeFinset) :
-- imply
  Sharpness.sources G (fun e => if e ∈ P then 1 else 0) = srcP P := by
-- proof
  apply StatMech.Ising.hnw_sources_indicator G P hP

/--
[hnw_addBackbone_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomNativeWeight.lean)
-/
@[path]
private lemma hnw_addBackbone_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Current V}
  {P : Finset (Sym2 V)}
-- given
  (hP : P ⊆ G.edgeFinset) :
-- imply
  Sharpness.sources G (fun e => m e + (if e ∈ P then 1 else 0)) = Sharpness.sources G m ∆ srcP P := by
-- proof
  apply StatMech.Ising.hnw_addBackbone_sources G m P hP

/--
[hnw_addBackbone_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomNativeWeight.lean)
-/
@[path]
private lemma hnw_addBackbone_weight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {P : Finset (Sym2 V)} :
-- imply
  Sharpness.weight G β J (fun e => m e + (if e ∈ P then 1 else 0)) = Sharpness.weight G β J m * ∏ e ∈ G.edgeFinset, (if e ∈ P then (β * J e) / (m e + 1) else 1) := by
-- proof
  apply StatMech.Ising.hnw_addBackbone_weight G β J m P


-- created on 2026-10-23
