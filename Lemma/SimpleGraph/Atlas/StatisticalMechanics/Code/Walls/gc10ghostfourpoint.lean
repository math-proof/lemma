import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc10ghostfourpoint
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc10_moment_oxyg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostfourpoint.lean)
-/
@[path]
private lemma gc10_moment_oxyg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) = isingExpectation G β h (fun s => spin s o * (spin s x * spin s y)) := by
-- proof
  apply StatMech.Walls.gc10_moment_oxyg G β h o x y hox hoy hxy

/--
[gc10_moment_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostfourpoint.lean)
-/
@[path]
private lemma gc10_moment_pair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x) :
-- imply
  expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (({o, x} : Finset V).map someEmb) = isingExpectation G β h (fun s => spin s o * spin s x) := by
-- proof
  apply StatMech.Walls.gc10_moment_pair G β h o x hox

/--
[gc10_moment_ghostSingle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostfourpoint.lean)
-/
@[path]
private lemma gc10_moment_ghostSingle_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {y : V}
-- given
  (β h : ℝ) :
-- imply
  expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({y} : Finset V).map someEmb)) = isingExpectation G β h (fun s => spin s y) := by
-- proof
  apply StatMech.Walls.gc10_moment_ghostSingle G β h y

/--
[gc10_ursell4_ghostPlus_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostfourpoint.lean)
-/
@[path]
private lemma gc10_ursell4_ghostPlus_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  eg_ursell4_ghostPlus G β h o x y = eg_ursell4_ghost G β h o x y := by
-- proof
  apply StatMech.Walls.gc10_ursell4_ghostPlus_eq G β h o x y hox hoy hxy

/--
[gc10_ghostFourPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostfourpoint.lean)
-/
@[path]
private lemma gc10_ghostFourPoint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  eg_ursell3 G β h o x y = eg_ursell4_ghostPlus G β h o x y + 2 * (onePt G β h o * onePt G β h x * onePt G β h y) := by
-- proof
  apply StatMech.Walls.gc10_ghostFourPoint G β h o x y hox hoy hxy

/--
[gc10_ursell4_ghostPlus_eq_ursell_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostfourpoint.lean)
-/
@[path]
private lemma gc10_ursell4_ghostPlus_eq_ursell_sub_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  eg_ursell4_ghostPlus G β h o x y = eg_ursell3 G β h o x y - 2 * (onePt G β h o * onePt G β h x * onePt G β h y) := by
-- proof
  apply StatMech.Walls.gc10_ursell4_ghostPlus_eq_ursell_sub G β h o x y hox hoy hxy

/--
[gc10_ghostFourPoint_eq_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostfourpoint.lean)
-/
@[path]
private lemma gc10_ghostFourPoint_eq_gap_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  eg_ursell4_ghostPlus G β h o x y = (cov3sym G β h o s(x, y) - ghsBoundSym G β h o s(x, y)) - 2 * (onePt G β h o * onePt G β h x * onePt G β h y) := by
-- proof
  apply StatMech.Walls.gc10_ghostFourPoint_eq_gap G β h o x y hox hoy hxy

/--
[gc10_ghs_iff_ghostFourPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostfourpoint.lean)
-/
@[path]
private lemma gc10_ghs_iff_ghostFourPoint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  cov3sym G β h o s(x, y) ≤ ghsBoundSym G β h o s(x, y) ↔ eg_ursell4_ghostPlus G β h o x y ≤ -2 * (onePt G β h o * onePt G β h x * onePt G β h y) := by
-- proof
  apply StatMech.Walls.gc10_ghs_iff_ghostFourPoint G β h o x y hox hoy hxy

/--
[gc10_ghostFourPoint_nonpos_degenerate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostfourpoint.lean)
-/
@[path]
private lemma gc10_ghostFourPoint_nonpos_degenerate_eq
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
  eg_ursell4_ghost G β h x x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc10_ghostFourPoint_nonpos_degenerate G β h hβ hh x y hxy

/--
[gc10_ghostFourPoint_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostfourpoint.lean)
-/
@[path]
private lemma gc10_ghostFourPoint_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  eg_ursell3 (⊤ : SimpleGraph (Fin 3)) 1 1 0 1 2 = eg_ursell4_ghostPlus (⊤ : SimpleGraph (Fin 3)) 1 1 0 1 2 + 2 * (onePt (⊤ : SimpleGraph (Fin 3)) 1 1 0 * onePt (⊤ : SimpleGraph (Fin 3)) 1 1 1 * onePt (⊤ : SimpleGraph (Fin 3)) 1 1 2) := by
-- proof
  apply StatMech.Walls.gc10_ghostFourPoint_nonvacuous G

/--
[gc10_ursell4_ghostPlus_eq_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostfourpoint.lean)
-/
@[path]
private lemma gc10_ursell4_ghostPlus_eq_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  eg_ursell4_ghostPlus (⊤ : SimpleGraph (Fin 3)) 1 1 0 1 2 = eg_ursell4_ghost (⊤ : SimpleGraph (Fin 3)) 1 1 0 1 2 := by
-- proof
  apply StatMech.Walls.gc10_ursell4_ghostPlus_eq_nonvacuous G


-- created on 2026-10-23
