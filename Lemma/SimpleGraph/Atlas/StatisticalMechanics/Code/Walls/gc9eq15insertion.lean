import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc9eq15insertion
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc9_sourceless_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9eq15insertion.lean)
-/
@[path]
private lemma gc9_sourceless_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ} :
-- imply
  0 < Sharpness.currentSum G β J ∅ := by
-- proof
  apply StatMech.Walls.gc9_sourceless_pos G β J

/--
[gc9_eq15_insertion_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9eq15insertion.lean)
-/
@[path]
private lemma gc9_eq15_insertion_of_ne_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (h0 : Sharpness.currentSum G β J ∅ ≠ 0) :
-- imply
  Sharpness.currentSum G β J A = Sharpness.expectationJ G β J A * Sharpness.currentSum G β J ∅ := by
-- proof
  apply StatMech.Walls.gc9_eq15_insertion_of_ne G β J A h0

/--
[gc9_eq15_insertion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9eq15insertion.lean)
-/
@[path]
private lemma gc9_eq15_insertion_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V} :
-- imply
  Sharpness.currentSum G β J A = Sharpness.expectationJ G β J A * Sharpness.currentSum G β J ∅ := by
-- proof
  apply StatMech.Walls.gc9_eq15_insertion G β J A

/--
[gc9_currentSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9eq15insertion.lean)
-/
@[path]
private lemma gc9_currentSum_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ Sharpness.currentSum G β J A := by
-- proof
  apply StatMech.Walls.gc9_currentSum_nonneg G β J hβ hJ A

/--
[gc9_expectationJ_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9eq15insertion.lean)
-/
@[path]
private lemma gc9_expectationJ_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ Sharpness.expectationJ G β J A := by
-- proof
  apply StatMech.Walls.gc9_expectationJ_nonneg G β J hβ hJ A

/--
[gc9_eq15_insertion_ghost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9eq15insertion.lean)
-/
@[path]
private lemma gc9_eq15_insertion_ghost_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {y : V}
-- given
  (β h : ℝ) :
-- imply
  Sharpness.currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({y} : Finset V).map someEmb)) = isingExpectation G β h (fun s => spin s y) * Sharpness.currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ := by
-- proof
  apply StatMech.Walls.gc9_eq15_insertion_ghost G β h y

/--
[gc9_eq15_insertion_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9eq15insertion.lean)
-/
@[path]
private lemma gc9_eq15_insertion_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {β : ℝ}
  {J : Sym2 (Fin 4) → ℝ} :
-- imply
  Sharpness.currentSum (⊥ : SimpleGraph (Fin 4)) β J ({1, 2} : Finset (Fin 4)) = Sharpness.expectationJ (⊥ : SimpleGraph (Fin 4)) β J ({1, 2} : Finset (Fin 4)) * Sharpness.currentSum (⊥ : SimpleGraph (Fin 4)) β J ∅ := by
-- proof
  apply StatMech.Walls.gc9_eq15_insertion_nonvacuous β J


-- created on 2026-10-23
