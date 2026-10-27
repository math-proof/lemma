import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc9Znormaliserpos
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc9_Z_normaliser_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9Znormaliserpos.lean)
-/
@[path]
private lemma gc9_Z_normaliser_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 (Option V) → ℝ} :
-- imply
  0 < gc9_Z_normaliser G β J := by
-- proof
  apply StatMech.Walls.gc9_Z_normaliser_pos G β J

/--
[gc9_Z_normaliser_pos_ghost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9Znormaliserpos.lean)
-/
@[path]
private lemma gc9_Z_normaliser_pos_ghost_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h : ℝ) :
-- imply
  0 < gc9_Z_normaliser G β (ghostCoupling h β (fun _ => 1)) := by
-- proof
  apply StatMech.Walls.gc9_Z_normaliser_pos_ghost G β h

/--
[gc9_Z_normaliser_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9Znormaliserpos.lean)
-/
@[path]
private lemma gc9_Z_normaliser_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 (Option V) → ℝ} :
-- imply
  gc9_Z_normaliser G β J ≠ 0 := by
-- proof
  apply StatMech.Walls.gc9_Z_normaliser_ne_zero G β J

/--
[gc9_Z_normaliser_ne_zero_ghost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9Znormaliserpos.lean)
-/
@[path]
private lemma gc9_Z_normaliser_ne_zero_ghost_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h : ℝ) :
-- imply
  gc9_Z_normaliser G β (ghostCoupling h β (fun _ => 1)) ≠ 0 := by
-- proof
  apply StatMech.Walls.gc9_Z_normaliser_ne_zero_ghost G β h

/--
[gc9_Z_normaliser_two_current](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9Znormaliserpos.lean)
-/
@[path]
private lemma gc9_Z_normaliser_two_current_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 (Option V) → ℝ} :
-- imply
  gc9_Z_normaliser G β J = Sharpness.currentSum (withGhost G) β J ∅ * Sharpness.currentSum (withGhost G) β J ∅ := by
-- proof
  apply StatMech.Walls.gc9_Z_normaliser_two_current G β J

/--
[gc9_Z_normaliser_eq_partition_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9Znormaliserpos.lean)
-/
@[path]
private lemma gc9_Z_normaliser_eq_partition_sq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 (Option V) → ℝ} :
-- imply
  gc9_Z_normaliser G β J = (Sharpness.partitionJ (withGhost G) β J / (2 : ℝ) ^ (Fintype.card (Option V))) ^ 2 := by
-- proof
  apply StatMech.Walls.gc9_Z_normaliser_eq_partition_sq G β J

/--
[gc9_Z_normaliser_instantiates_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9Znormaliserpos.lean)
-/
@[path]
private lemma gc9_Z_normaliser_instantiates_bridge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 (Option V) → ℝ}
  {o x y : V}
  {D : ℝ}
-- given
  (β h : ℝ)
  (hD : 0 ≤ D)
  (hid : eg_ursell3 G β h o x y * gc9_Z_normaliser G β J = -D) :
-- imply
  ∃ (D' Z' : ℝ), (0 ≤ D') ∧ (0 < Z') ∧ eg_ursell3 G β h o x y * Z' = - D' := by
-- proof
  apply StatMech.Walls.gc9_Z_normaliser_instantiates_bridge G β h J o x y D hD hid

/--
[gc9_Z_normaliser_pos_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9Znormaliserpos.lean)
-/
@[path]
private lemma gc9_Z_normaliser_pos_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  0 < gc9_Z_normaliser (⊤ : SimpleGraph (Fin 3)) 1 (ghostCoupling 1 1 (fun _ => 1)) := by
-- proof
  apply StatMech.Walls.gc9_Z_normaliser_pos_nonvacuous G


-- created on 2026-10-23
