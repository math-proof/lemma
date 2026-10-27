import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.EnsembleGHS
open Finset Classical StatMech StatMech.Ising


/--
[egh_ensemble_ursell_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/EnsembleGHS.lean)
-/
@[path]
private lemma egh_ensemble_ursell_eq_eq
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
  egh_ensembleUrsell G β J M B o x y = -2 * tcp_allConnMass G β J M B o x y := by
-- proof
  apply StatMech.Ising.egh_ensemble_ursell_eq G β J M B hox hoy hxy

/--
[egh_ensemble_domination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/EnsembleGHS.lean)
-/
@[path]
private lemma egh_ensemble_domination_eq
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
  apply StatMech.Ising.egh_ensemble_domination G β J hβ hJ M B o x y

/--
[egh_ensemble_prob_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/EnsembleGHS.lean)
-/
@[path]
private lemma egh_ensemble_prob_le_one_eq
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
  apply StatMech.Ising.egh_ensemble_prob_le_one G β J hβ hJ M B o x y

/--
[egh_ensemble_ursell_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/EnsembleGHS.lean)
-/
@[path]
private lemma egh_ensemble_ursell_sign_eq
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
  egh_ensembleUrsell G β J M B o x y ≤ 0 := by
-- proof
  apply StatMech.Ising.egh_ensemble_ursell_sign G β J hβ hJ M B hox hoy hxy

/--
[egh_ghs_distinct_site_ensemble](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/EnsembleGHS.lean)
-/
@[path]
private lemma egh_ghs_distinct_site_ensemble_eq
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
  apply StatMech.Ising.egh_ghs_distinct_site_ensemble G β J hβ hJ M B hox hoy hxy

/--
[egh_eq_gri2_ensemble](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/EnsembleGHS.lean)
-/
@[path]
private lemma egh_eq_gri2_ensemble_eq
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
  apply StatMech.Ising.egh_eq_gri2_ensemble G β J hβ hJ M hnd B hm huv hcoh

/--
[egh_u3_nonpos_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/EnsembleGHS.lean)
-/
@[path]
private lemma egh_u3_nonpos_bound_eq
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
  apply StatMech.Ising.egh_u3_nonpos_bound G β J hβ hJ M B o x y μ hμ

/--
[egh_u3_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/EnsembleGHS.lean)
-/
@[path]
private lemma egh_u3_nonpos_eq
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
  -2 * μ * tcp_allConnProb G β J M B o x y ≤ 0 := by
-- proof
  apply StatMech.Ising.egh_u3_nonpos G β J hβ hJ M B o x y μ hμ

/--
[egh_lebowitz_quantitative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/EnsembleGHS.lean)
-/
@[path]
private lemma egh_lebowitz_quantitative_eq
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
  -2 * μ ≤ -2 * μ * tcp_allConnProb G β J M B o x y := by
-- proof
  apply StatMech.Ising.egh_lebowitz_quantitative G β J hβ hJ M B o x y μ hμ

/--
[egh_aizenman_barsky_sharpness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/EnsembleGHS.lean)
-/
@[path]
private lemma egh_aizenman_barsky_sharpness_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {Jsum : ℝ}
-- given
  (β h : ℝ)
  (hghs : GHSThreePointSym G β h o)
  (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e = Jsum * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
-- imply
  bondEnergySusceptibility G β h o ≤ Jsum * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
-- proof
  apply StatMech.Ising.egh_aizenman_barsky_sharpness G β h o Jsum hghs hfactor


-- created on 2026-10-23
