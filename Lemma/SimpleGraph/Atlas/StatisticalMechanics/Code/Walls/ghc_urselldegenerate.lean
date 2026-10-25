import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.ghc_urselldegenerate
open Finset SimpleGraph Set StatMech StatMech.Walls


/--
[ursell3_eq_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_urselldegenerate.lean)
-/
@[path]
private lemma ursell3_eq_gap_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  ursell3 G β h o x y = cov3sym G β h o s(x, y) - ghsBoundSym G β h o s(x, y) := by
-- proof
  apply StatMech.Walls.ursell3_eq_gap G β h o x y

/--
[ghc_u3_degenerate_eq_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_urselldegenerate.lean)
-/
@[path]
private lemma ghc_u3_degenerate_eq_gap_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
-- given
  (β h : ℝ) :
-- imply
  ursell3 G β h x x y = -2 * isingExpectation G β h (fun s => spin s x) * cov2 G β h x y := by
-- proof
  apply StatMech.Walls.ghc_u3_degenerate_eq_gap G β h x y

/--
[ghc_ursell_degenerate_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_urselldegenerate.lean)
-/
@[path]
private lemma ghc_ursell_degenerate_left_eq
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
  ursell3 G β h x x y ≤ 0 := by
-- proof
  apply StatMech.Walls.ghc_ursell_degenerate_left G β h hβ hh x y hxy

/--
[ghc_ursell_degenerate_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_urselldegenerate.lean)
-/
@[path]
private lemma ghc_ursell_degenerate_right_eq
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
  ursell3 G β h y x y ≤ 0 := by
-- proof
  apply StatMech.Walls.ghc_ursell_degenerate_right G β h hβ hh x y hxy

/--
[ghc_ursell_degenerate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_urselldegenerate.lean)
-/
@[path]
private lemma ghc_ursell_degenerate_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hxy : x ≠ y)
  (hoxy : o = x ∨ o = y) :
-- imply
  ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.ghc_ursell_degenerate G β h hβ hh o x y hxy hoxy

/--
[ghc_ursell_degenerate_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_urselldegenerate.lean)
-/
@[path]
private lemma ghc_ursell_degenerate_of_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {e : Sym2 V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (he : e ∈ G.edgeFinset)
  (hoe : o ∈ e) :
-- imply
  cov3sym G β h o e - ghsBoundSym G β h o e ≤ 0 := by
-- proof
  apply StatMech.Walls.ghc_ursell_degenerate_of_mem G β h hβ hh o e he hoe


-- created on 2026-10-23
