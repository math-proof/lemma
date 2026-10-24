import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.TwoCurrentProbBound
open Finset Classical StatMech StatMech.Ising


/--
[tcp_partitionFunction_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoCurrentProbBound.lean)
-/
@[path]
private lemma tcp_partitionFunction_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {B : Finset V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ tcp_partitionFunction G β J M B := by
-- proof
  apply StatMech.Ising.tcp_partitionFunction_nonneg G β J hβ hJ M B

/--
[tcp_allConnMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoCurrentProbBound.lean)
-/
@[path]
private lemma tcp_allConnMass_nonneg_eq
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
  0 ≤ tcp_allConnMass G β J M B o x y := by
-- proof
  apply StatMech.Ising.tcp_allConnMass_nonneg G β J hβ hJ M B o x y

/--
[tcp_allConnMass_le_partitionFunction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoCurrentProbBound.lean)
-/
@[path]
private lemma tcp_allConnMass_le_partitionFunction_eq
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
  apply StatMech.Ising.tcp_allConnMass_le_partitionFunction G β J hβ hJ M B o x y

/--
[tcp_allConn_prob_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoCurrentProbBound.lean)
-/
@[path]
private lemma tcp_allConn_prob_le_one_eq
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
  apply StatMech.Ising.tcp_allConn_prob_le_one G β J hβ hJ M B o x y

/--
[tcp_allConn_prob_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoCurrentProbBound.lean)
-/
@[path]
private lemma tcp_allConn_prob_nonneg_eq
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
  0 ≤ tcp_allConnProb G β J M B o x y := by
-- proof
  apply StatMech.Ising.tcp_allConn_prob_nonneg G β J hβ hJ M B o x y

/--
[tcp_lebowitz_summed_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoCurrentProbBound.lean)
-/
@[path]
private lemma tcp_lebowitz_summed_gap_eq
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
  apply StatMech.Ising.tcp_lebowitz_summed_gap G β J M B hox hoy hxy

/--
[tcp_lebowitz_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoCurrentProbBound.lean)
-/
@[path]
private lemma tcp_lebowitz_sign_eq
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
  apply StatMech.Ising.tcp_lebowitz_sign G β J hβ hJ M B hox hoy hxy

/--
[tcp_reroute_sum_eq_three_allConnMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoCurrentProbBound.lean)
-/
@[path]
private lemma tcp_reroute_sum_eq_three_allConnMass_eq
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
  (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m (B ∆ {x, y})) + (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m (B ∆ {o, y})) + (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m (B ∆ {o, x})) = 3 * tcp_allConnMass G β J M B o x y := by
-- proof
  apply StatMech.Ising.tcp_reroute_sum_eq_three_allConnMass G β J M B hox hoy hxy

/--
[tcp_ghs_distinct_site](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoCurrentProbBound.lean)
-/
@[path]
private lemma tcp_ghs_distinct_site_eq
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
  ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B ≤ (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m (B ∆ {x, y})) + (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m (B ∆ {o, y})) + (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m (B ∆ {o, x})) := by
-- proof
  apply StatMech.Ising.tcp_ghs_distinct_site G β J hβ hJ M B hox hoy hxy

/--
[tcp_per_current_dom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoCurrentProbBound.lean)
-/
@[path]
private lemma tcp_per_current_dom_eq
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
  apply StatMech.Ising.tcp_per_current_dom G β J hβ hJ m hnd B hm huv hconn

/--
[tcp_family_prob_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoCurrentProbBound.lean)
-/
@[path]
private lemma tcp_family_prob_le_one_eq
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
  apply StatMech.Ising.tcp_family_prob_le_one G β J hβ hJ M hnd B hm huv hcoh

/--
[tcp_prob_bound_closes_lebowitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoCurrentProbBound.lean)
-/
@[path]
private lemma tcp_prob_bound_closes_lebowitz_eq
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
  apply StatMech.Ising.tcp_prob_bound_closes_lebowitz G β J hβ hJ M B o x y μ hμ


-- created on 2026-10-23
