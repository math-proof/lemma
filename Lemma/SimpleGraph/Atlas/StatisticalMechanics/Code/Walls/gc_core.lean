import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc_core
open Finset SimpleGraph Set StatMech StatMech.Walls


/--
[gc_ursell_eq_lebowitz_plus_triple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc_core.lean)
-/
@[path]
private lemma gc_ursell_eq_lebowitz_plus_triple_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  eg_ursell3 G β h o x y = gc_lebowitzU4 G β h o x y + 2 * isingExpectation G β h (fun s => spin s o) * isingExpectation G β h (fun s => spin s x) * isingExpectation G β h (fun s => spin s y) := by
-- proof
  apply StatMech.Walls.gc_ursell_eq_lebowitz_plus_triple G β h o x y

/--
[gc_triple_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc_core.lean)
-/
@[path]
private lemma gc_triple_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ 2 * isingExpectation G β h (fun s => spin s o) * isingExpectation G β h (fun s => spin s x) * isingExpectation G β h (fun s => spin s y) := by
-- proof
  apply StatMech.Walls.gc_triple_nonneg G β h hβ hh o x y

/--
[gc_lebowitz_le_ursell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc_core.lean)
-/
@[path]
private lemma gc_lebowitz_le_ursell_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  gc_lebowitzU4 G β h o x y ≤ eg_ursell3 G β h o x y := by
-- proof
  apply StatMech.Walls.gc_lebowitz_le_ursell G β h hβ hh o x y

/--
[gc_ursell_nonpos_degenerate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc_core.lean)
-/
@[path]
private lemma gc_ursell_nonpos_degenerate_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hxy : x ≠ y) :
-- imply
  eg_ursell3 G β h x x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc_ursell_nonpos_degenerate G β h hβ hh x y hxy

/--
[gc_ursell_xeqy_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc_core.lean)
-/
@[path]
private lemma gc_ursell_xeqy_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x) :
-- imply
  eg_ursell3 G β h o x x ≤ 0 := by
-- proof
  apply StatMech.Walls.gc_ursell_xeqy_nonpos G β h hβ hh o x hox

/--
[gc_ursell_nonpos_of_signDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc_core.lean)
-/
@[path]
private lemma gc_ursell_nonpos_of_signDominance_eq
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
  apply StatMech.Walls.gc_ursell_nonpos_of_signDominance G β h hβ hh o hsd x y

/--
[gc_ghs_concavity_of_signDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc_core.lean)
-/
@[path]
private lemma gc_ghs_concavity_of_signDominance_eq
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
  apply StatMech.Walls.gc_ghs_concavity_of_signDominance G β h hβ hh o hsd

/--
[gc_aizenman_barsky_of_signDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc_core.lean)
-/
@[path]
private lemma gc_aizenman_barsky_of_signDominance_eq
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
  apply StatMech.Walls.gc_aizenman_barsky_of_signDominance G β h hβ hh o J hsd hfactor

/--
[gc_spinProd_triple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc_core.lean)
-/
@[path]
private lemma gc_spinProd_triple_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  spinProd ({o, x, y} : Finset V) = (fun s => spin s o * (spin s x * spin s y)) := by
-- proof
  apply StatMech.Walls.gc_spinProd_triple G hox hoy hxy

/--
[gc_ursell_currentSum_rep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc_core.lean)
-/
@[path]
private lemma gc_ursell_currentSum_rep_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  eg_ursell3 G β 0 o x y = currentSum G β (fun _ => 1) {o, x, y} / currentSum G β (fun _ => 1) ∅ - currentSum G β (fun _ => 1) {o} / currentSum G β (fun _ => 1) ∅ * (currentSum G β (fun _ => 1) {x, y} / currentSum G β (fun _ => 1) ∅) - currentSum G β (fun _ => 1) {o, x} / currentSum G β (fun _ => 1) ∅ * (currentSum G β (fun _ => 1) {y} / currentSum G β (fun _ => 1) ∅) - currentSum G β (fun _ => 1) {o, y} / currentSum G β (fun _ => 1) ∅ * (currentSum G β (fun _ => 1) {x} / currentSum G β (fun _ => 1) ∅) + 2 * (currentSum G β (fun _ => 1) {o} / currentSum G β (fun _ => 1) ∅) * (currentSum G β (fun _ => 1) {x} / currentSum G β (fun _ => 1) ∅) * (currentSum G β (fun _ => 1) {y} / currentSum G β (fun _ => 1) ∅) := by
-- proof
  apply StatMech.Walls.gc_ursell_currentSum_rep G β hox hoy hxy


-- created on 2026-10-23
