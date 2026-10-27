import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.ghc_urselleqgap
open Finset SimpleGraph Set StatMech StatMech.Walls StatMech.Walls.GhcEqGap


/--
[ghc_ursellEqGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_urselleqgap.lean)
-/
@[path]
private lemma ghc_ursellEqGap_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  cov3sym G β h o s(x, y) - ghsBoundSym G β h o s(x, y) = eg_ursell3 G β h o x y := by
-- proof
  apply StatMech.Walls.GhcEqGap.ghc_ursellEqGap G β h o x y

/--
[ghc_ursell_nonpos_iff_ghs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_urselleqgap.lean)
-/
@[path]
private lemma ghc_ursell_nonpos_iff_ghs_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 ↔ cov3sym G β h o s(x, y) ≤ ghsBoundSym G β h o s(x, y) := by
-- proof
  apply StatMech.Walls.GhcEqGap.ghc_ursell_nonpos_iff_ghs G β h o x y

/--
[ghc_ursell_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_urselleqgap.lean)
-/
@[path]
private lemma ghc_ursell_swap_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  eg_ursell3 G β h o x y = eg_ursell3 G β h o y x := by
-- proof
  apply StatMech.Walls.GhcEqGap.ghc_ursell_swap G β h o x y

/--
[ghc_ghs_of_ursell_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_urselleqgap.lean)
-/
@[path]
private lemma ghc_ghs_of_ursell_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (h0 : ∀ x y : V, eg_ursell3 G β h o x y ≤ 0) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.GhcEqGap.ghc_ghs_of_ursell_nonpos G β h o h0

/--
[ghc_ursell_nonpos_of_ghs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_urselleqgap.lean)
-/
@[path]
private lemma ghc_ursell_nonpos_of_ghs_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {x y : V}
-- given
  (β h : ℝ)
  (hghs : GHSThreePointSym G β h o)
  (he : s(x, y) ∈ G.edgeFinset) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.GhcEqGap.ghc_ursell_nonpos_of_ghs G β h o hghs he

/--
[ghc_ghsSym_iff_ursell_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_urselleqgap.lean)
-/
@[path]
private lemma ghc_ghsSym_iff_ursell_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ) :
-- imply
  GHSThreePointSym G β h o ↔ ∀ x y : V, s(x, y) ∈ G.edgeFinset → eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.GhcEqGap.ghc_ghsSym_iff_ursell_nonpos G β h o

/--
[ghc_ursell_degenerate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_urselleqgap.lean)
-/
@[path]
private lemma ghc_ursell_degenerate_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
-- given
  (β h : ℝ) :
-- imply
  eg_ursell3 G β h x x y = -2 * isingExpectation G β h (fun s => spin s x) * cov2 G β h x y := by
-- proof
  apply StatMech.Walls.GhcEqGap.ghc_ursell_degenerate G β h x y

/--
[ghc_ursell_nonpos_degenerate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_urselleqgap.lean)
-/
@[path]
private lemma ghc_ursell_nonpos_degenerate_eq
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
  apply StatMech.Walls.GhcEqGap.ghc_ursell_nonpos_degenerate G β h hβ hh x y hxy

/--
[ghc_aizenman_barsky_of_ursell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_urselleqgap.lean)
-/
@[path]
private lemma ghc_aizenman_barsky_of_ursell_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {J : ℝ}
-- given
  (β h : ℝ)
  (h0 : ∀ x y : V, eg_ursell3 G β h o x y ≤ 0)
  (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
-- imply
  bondEnergySusceptibility G β h o ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
-- proof
  apply StatMech.Walls.GhcEqGap.ghc_aizenman_barsky_of_ursell G β h o J h0 hfactor


-- created on 2026-10-23
