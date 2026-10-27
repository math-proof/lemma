import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc8innereq15
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc8_inner_eq15](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8innereq15.lean)
-/
@[path]
private lemma gc8_inner_eq15_eq
  [Fintype V]
  [DecidableEq V]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {y g : V} :
-- imply
  Sharpness.currentSum S β J ({y, g} : Finset V) = Sharpness.expectationJ S β J ({y, g} : Finset V) * Sharpness.currentSum S β J ∅ := by
-- proof
  apply StatMech.Walls.gc8_inner_eq15 S β J y g

/--
[gc8_inner_eq15_ratio_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8innereq15.lean)
-/
@[path]
private lemma gc8_inner_eq15_ratio_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {y g : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ Sharpness.expectationJ S β J ({y, g} : Finset V) := by
-- proof
  apply StatMech.Walls.gc8_inner_eq15_ratio_nonneg S β J hβ hJ y g

/--
[gc8_inner_eq15_sourceless_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8innereq15.lean)
-/
@[path]
private lemma gc8_inner_eq15_sourceless_pos_eq
  [Fintype V]
  [DecidableEq V]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ} :
-- imply
  0 < Sharpness.currentSum S β J ∅ := by
-- proof
  apply StatMech.Walls.gc8_inner_eq15_sourceless_pos S β J

/--
[gc8_inner_eq15_lhs_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8innereq15.lean)
-/
@[path]
private lemma gc8_inner_eq15_lhs_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {y g : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ Sharpness.currentSum S β J ({y, g} : Finset V) := by
-- proof
  apply StatMech.Walls.gc8_inner_eq15_lhs_nonneg S β J hβ hJ y g

/--
[gc8_inner_eq15_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8innereq15.lean)
-/
@[path]
private lemma gc8_inner_eq15_sq_eq
  [Fintype V]
  [DecidableEq V]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {y g : V} :
-- imply
  Sharpness.expectationJ S β J ({y, g} : Finset V) * Sharpness.currentSum S β J ({y, g} : Finset V) = (Sharpness.expectationJ S β J ({y, g} : Finset V)) ^ 2 * Sharpness.currentSum S β J ∅ := by
-- proof
  apply StatMech.Walls.gc8_inner_eq15_sq S β J y g

/--
[gc8_inner_eq15_claim1_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8innereq15.lean)
-/
@[path]
private lemma gc8_inner_eq15_claim1_step_eq
  [Fintype V]
  [DecidableEq V]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {y g : V}
  {eΛ : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hgriff : Sharpness.expectationJ S β J ({y, g} : Finset V) ≤ eΛ) :
-- imply
  eΛ * Sharpness.currentSum S β J ({y, g} : Finset V) ≥ (Sharpness.expectationJ S β J ({y, g} : Finset V)) ^ 2 * Sharpness.currentSum S β J ∅ := by
-- proof
  apply StatMech.Walls.gc8_inner_eq15_claim1_step S β J hβ hJ y g eΛ hgriff

/--
[gc8_inner_eq15_ghost_magnetization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8innereq15.lean)
-/
@[path]
private lemma gc8_inner_eq15_ghost_magnetization_eq
  [Fintype V]
  [DecidableEq V]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {y : V}
-- given
  (β h : ℝ) :
-- imply
  expectationJ (withGhost S) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({y} : Finset V).map someEmb)) = isingExpectation S β h (fun s => spin s y) := by
-- proof
  apply StatMech.Walls.gc8_inner_eq15_ghost_magnetization S β h y

/--
[gc8_inner_eq15_magnetization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8innereq15.lean)
-/
@[path]
private lemma gc8_inner_eq15_magnetization_eq
  [Fintype V]
  [DecidableEq V]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {y : V}
-- given
  (β h : ℝ) :
-- imply
  Sharpness.currentSum (withGhost S) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({y} : Finset V).map someEmb)) = isingExpectation S β h (fun s => spin s y) * Sharpness.currentSum (withGhost S) β (ghostCoupling h β (fun _ => 1)) ∅ := by
-- proof
  apply StatMech.Walls.gc8_inner_eq15_magnetization S β h y

/--
[gc8_inner_eq15_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8innereq15.lean)
-/
@[path]
private lemma gc8_inner_eq15_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {β : ℝ}
  {J : Sym2 (Fin 4) → ℝ} :
-- imply
  Sharpness.currentSum (⊥ : SimpleGraph (Fin 4)) β J ({1, 2} : Finset (Fin 4)) = Sharpness.expectationJ (⊥ : SimpleGraph (Fin 4)) β J ({1, 2} : Finset (Fin 4)) * Sharpness.currentSum (⊥ : SimpleGraph (Fin 4)) β J ∅ := by
-- proof
  apply StatMech.Walls.gc8_inner_eq15_nonvacuous β J


-- created on 2026-10-23
