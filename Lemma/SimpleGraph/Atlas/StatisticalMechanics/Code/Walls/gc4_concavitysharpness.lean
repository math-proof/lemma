import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc4_concavitysharpness
open Finset SimpleGraph Set StatMech StatMech.Walls


/--
[gc4_hasDerivAt_cov2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_concavitysharpness.lean)
-/
@[path]
private lemma gc4_hasDerivAt_cov2_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x : V}
-- given
  (β h : ℝ) :
-- imply
  HasDerivAt (fun h => cov2 G β h o x) (gc4_D1cov2 G β h o x) h := by
-- proof
  apply StatMech.Walls.gc4_hasDerivAt_cov2 G β h o x

/--
[gc4_D1cov2_eq_sum_u3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_concavitysharpness.lean)
-/
@[path]
private lemma gc4_D1cov2_eq_sum_u3_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x : V}
-- given
  (β h : ℝ) :
-- imply
  gc4_D1cov2 G β h o x = β * ∑ y, eg_ursell3 G β h o x y := by
-- proof
  apply StatMech.Walls.gc4_D1cov2_eq_sum_u3 G β h o x

/--
[gc4_deriv_magnetization_eq_fun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_concavitysharpness.lean)
-/
@[path]
private lemma gc4_deriv_magnetization_eq_fun_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o : V} :
-- imply
  deriv (fun h => isingExpectation G β h (fun s => spin s o)) = (fun h => β * ∑ x, cov2 G β h o x) := by
-- proof
  apply StatMech.Walls.gc4_deriv_magnetization_eq_fun G β o

/--
[gc4_hasDerivAt_sumcov2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_concavitysharpness.lean)
-/
@[path]
private lemma gc4_hasDerivAt_sumcov2_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ) :
-- imply
  HasDerivAt (fun h => β * ∑ x, cov2 G β h o x) (β * ∑ x, gc4_D1cov2 G β h o x) h := by
-- proof
  apply StatMech.Walls.gc4_hasDerivAt_sumcov2 G β h o

/--
[gc4_hasDerivAt_deriv_magnetization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_concavitysharpness.lean)
-/
@[path]
private lemma gc4_hasDerivAt_deriv_magnetization_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ) :
-- imply
  HasDerivAt (deriv (fun h => isingExpectation G β h (fun s => spin s o))) (β * (β * ∑ x, ∑ y, eg_ursell3 G β h o x y)) h := by
-- proof
  apply StatMech.Walls.gc4_hasDerivAt_deriv_magnetization G β h o

/--
[gc4_deriv2_magnetization_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_concavitysharpness.lean)
-/
@[path]
private lemma gc4_deriv2_magnetization_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ) :
-- imply
  deriv^[2] (fun h => isingExpectation G β h (fun s => spin s o)) h = β * (β * ∑ x, ∑ y, eg_ursell3 G β h o x y) := by
-- proof
  apply StatMech.Walls.gc4_deriv2_magnetization_eq G β h o

/--
[gc4_deriv2_magnetization_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_concavitysharpness.lean)
-/
@[path]
private lemma gc4_deriv2_magnetization_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o : V}
-- given
  (hβ : 0 ≤ β)
  (h : ℝ)
  (hh : 0 ≤ h)
  (hsd : GHSSignDominance G β h o) :
-- imply
  deriv^[2] (fun h => isingExpectation G β h (fun s => spin s o)) h ≤ 0 := by
-- proof
  apply StatMech.Walls.gc4_deriv2_magnetization_nonpos G β hβ o h hh hsd

/--
[gc4_magnetization_concaveOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_concavitysharpness.lean)
-/
@[path]
private lemma gc4_magnetization_concaveOn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o : V}
-- given
  (hβ : 0 ≤ β)
  (hsd : ∀ h, 0 ≤ h → GHSSignDominance G β h o) :
-- imply
  ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o)) := by
-- proof
  apply StatMech.Walls.gc4_magnetization_concaveOn G β hβ o hsd

/--
[gc4_ursell_nonpos_of_signDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_concavitysharpness.lean)
-/
@[path]
private lemma gc4_ursell_nonpos_of_signDominance_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hsd : GHSSignDominance G β h o) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc4_ursell_nonpos_of_signDominance G β h hβ hh o hsd x y

/--
[gc4_ghs_concavity_of_signDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_concavitysharpness.lean)
-/
@[path]
private lemma gc4_ghs_concavity_of_signDominance_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hsd : GHSSignDominance G β h o) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.gc4_ghs_concavity_of_signDominance G β h hβ hh o hsd

/--
[gc4_aizenman_barsky_of_signDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_concavitysharpness.lean)
-/
@[path]
private lemma gc4_aizenman_barsky_of_signDominance_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {J : ℝ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hsd : GHSSignDominance G β h o)
  (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
-- imply
  bondEnergySusceptibility G β h o ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
-- proof
  apply StatMech.Walls.gc4_aizenman_barsky_of_signDominance G β h hβ hh o J hsd hfactor

/--
[gc4_concavitySharpness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_concavitysharpness.lean)
-/
@[path]
private lemma gc4_concavitySharpness_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {J : ℝ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hsd : ∀ h', 0 ≤ h' → GHSSignDominance G β h' o)
  (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
-- imply
  GHSThreePointSym G β h o ∧ ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o)) ∧ bondEnergySusceptibility G β h o ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
-- proof
  apply StatMech.Walls.gc4_concavitySharpness G β h hβ hh o J hsd hfactor


-- created on 2026-10-23
