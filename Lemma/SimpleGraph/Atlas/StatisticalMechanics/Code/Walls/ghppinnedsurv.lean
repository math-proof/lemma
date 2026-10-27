import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.ghppinnedsurv.Part2
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[ghp_survConcrete_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghppinnedsurv.lean)
-/
@[path]
private lemma ghp_survConcrete_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (β h : ℝ) :
-- imply
  ghp_survConcrete G β h i j k = StatMech.Ising.cov2 G β h i j * StatMech.Ising.cov2 G β h j k - StatMech.Walls.VBG.vbg_var (StatMech.Ising.isingProb G β h) (fun s => StatMech.Ising.spin s j) * StatMech.Ising.cov2 G β h i k := by
-- proof
  apply StatMech.Walls.ghp_survConcrete_eq G β h i j k

/--
[ghp_surv_le_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghppinnedsurv.lean)
-/
@[path]
private lemma ghp_surv_le_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β) :
-- imply
  ghp_survConcrete G β h i j k ≤ 0 := by
-- proof
  apply StatMech.Walls.ghp_surv_le_zero G β h hβ i j k

/--
[ghp_ghs_of_pinned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghppinnedsurv.lean)
-/
@[path]
private lemma ghp_ghs_of_pinned_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y i j k : V}
  {dropA dropB : ℝ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hident : eg_ursell3 G β h o x y = ghp_survConcrete G β h i j k - 2 * dropA - 2 * dropB)
  (hdropA : 0 ≤ dropA)
  (hdropB : 0 ≤ dropB) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.ghp_ghs_of_pinned G β h hβ o x y i j k hident hdropA hdropB

/--
[ghp_ghs_of_eq22_pinned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghppinnedsurv.lean)
-/
@[path]
private lemma ghp_ghs_of_eq22_pinned_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hres : ghp_eq22_pinned G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.ghp_ghs_of_eq22_pinned G β h hβ o x y hres

/--
[ghp_pinned_forces_ghs_all_fields](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghppinnedsurv.lean)
-/
@[path]
private lemma ghp_pinned_forces_ghs_all_fields_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hres : ghp_eq22_pinned G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.ghp_pinned_forces_ghs_all_fields G β h hβ o x y hres

/--
[ghp_surv_is_twoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghppinnedsurv.lean)
-/
@[path]
private lemma ghp_surv_is_twoPoint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v : V}
-- given
  (β h : ℝ) :
-- imply
  eg_ursell3 G β h v v v = 2 * (isingExpectation G β h (fun s => spin s v))^3 - 2 * isingExpectation G β h (fun s => spin s v) := by
-- proof
  apply StatMech.Walls.ghp_surv_is_twoPoint G β h v

/--
[ghp_eq22_pinned_of_ghs_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghppinnedsurv.lean)
-/
@[path]
private lemma ghp_eq22_pinned_of_ghs_dominated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hdom : eg_ursell3 G β h o x y ≤ ghp_survConcrete G β h o o o) :
-- imply
  ghp_eq22_pinned G β h o x y := by
-- proof
  apply StatMech.Walls.ghp_eq22_pinned_of_ghs_dominated G β h o x y hdom

/--
[ghp_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghppinnedsurv.lean)
-/
@[path]
private lemma ghp_status_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  True := by
-- proof
  apply StatMech.Walls.ghp_status


-- created on 2026-10-23
