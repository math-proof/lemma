import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc8reinnerpair
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc8r_reinner_pair_eq15sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8reinnerpair.lean)
-/
@[path]
private lemma gc8r_reinner_pair_eq15sq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {GS : SimpleGraph V}
  [DecidableRel GS.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (h0 : Sharpness.currentSum GS β J ∅ ≠ 0) :
-- imply
  Sharpness.expectationJ GS β J A * Sharpness.currentSum GS β J A = (Sharpness.expectationJ GS β J A) ^ 2 * Sharpness.currentSum GS β J ∅ := by
-- proof
  apply StatMech.Walls.gc8r_reinner_pair_eq15sq G GS β J A h0

/--
[gc8r_reinner_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8reinnerpair.lean)
-/
@[path]
private lemma gc8r_reinner_pair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {GS : SimpleGraph V}
  [DecidableRel GS.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (hc : 0 < Sharpness.currentSum GS β J ∅) :
-- imply
  (Sharpness.expectationJ GS β J A) ^ 2 * Sharpness.currentSum GS β J ∅ = (Sharpness.currentSum GS β J A) ^ 2 / Sharpness.currentSum GS β J ∅ := by
-- proof
  apply StatMech.Walls.gc8r_reinner_pair G GS β J A hc

/--
[gc8r_reinner_pair_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8reinnerpair.lean)
-/
@[path]
private lemma gc8r_reinner_pair_unconditional_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {GS : SimpleGraph V}
  [DecidableRel GS.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V} :
-- imply
  (Sharpness.expectationJ GS β J A) ^ 2 * Sharpness.currentSum GS β J ∅ = (Sharpness.currentSum GS β J A) ^ 2 / Sharpness.currentSum GS β J ∅ := by
-- proof
  apply StatMech.Walls.gc8r_reinner_pair_unconditional G GS β J A

/--
[gc8r_reinner_pair_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8reinnerpair.lean)
-/
@[path]
private lemma gc8r_reinner_pair_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {GS : SimpleGraph V}
  [DecidableRel GS.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V} :
-- imply
  ((Sharpness.expectationJ GS β J A) ^ 2 * Sharpness.currentSum GS β J ∅) * Sharpness.currentSum GS β J ∅ = (Sharpness.currentSum GS β J A) ^ 2 := by
-- proof
  apply StatMech.Walls.gc8r_reinner_pair_mul G GS β J A

/--
[gc8r_squared_mass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8reinnerpair.lean)
-/
@[path]
private lemma gc8r_squared_mass_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {GS : SimpleGraph V}
  [DecidableRel GS.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ (Sharpness.expectationJ GS β J A) ^ 2 * Sharpness.currentSum GS β J ∅ := by
-- proof
  apply StatMech.Walls.gc8r_squared_mass_nonneg G GS β J hβ hJ A

/--
[gc8r_reinner_pair_ghost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8reinnerpair.lean)
-/
@[path]
private lemma gc8r_reinner_pair_ghost_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {GS : SimpleGraph V}
  [DecidableRel GS.Adj]
  {y : V}
-- given
  (β h : ℝ) :
-- imply
  (isingExpectation GS β h (fun s => spin s y)) ^ 2 * currentSum (withGhost GS) β (FieldGhostDict.ghostCoupling h β (fun _ => 1)) ∅ = (currentSum (withGhost GS) β (FieldGhostDict.ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({y} : Finset V).map FieldGhostDict.someEmb))) ^ 2 / currentSum (withGhost GS) β (FieldGhostDict.ghostCoupling h β (fun _ => 1)) ∅ := by
-- proof
  apply StatMech.Walls.gc8r_reinner_pair_ghost G GS β h y

/--
[gc8r_reinner_pair_griffiths_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8reinnerpair.lean)
-/
@[path]
private lemma gc8r_reinner_pair_griffiths_chain_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {GS : SimpleGraph V}
  [DecidableRel GS.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {eΛ : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hgriff : Sharpness.expectationJ GS β J A ≤ eΛ) :
-- imply
  eΛ * Sharpness.currentSum GS β J A ≥ (Sharpness.currentSum GS β J A) ^ 2 / Sharpness.currentSum GS β J ∅ := by
-- proof
  apply StatMech.Walls.gc8r_reinner_pair_griffiths_chain G GS β J A eΛ hβ hJ hgriff

/--
[gc8r_reinner_pair_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8reinnerpair.lean)
-/
@[path]
private lemma gc8r_reinner_pair_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  (isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (fun s => spin s 0)) ^ 2 * currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (FieldGhostDict.ghostCoupling 1 1 (fun _ => 1)) ∅ = (currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (FieldGhostDict.ghostCoupling 1 1 (fun _ => 1)) (insert (none : Option (Fin 3)) (({0} : Finset (Fin 3)).map FieldGhostDict.someEmb))) ^ 2 / currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (FieldGhostDict.ghostCoupling 1 1 (fun _ => 1)) ∅ := by
-- proof
  apply StatMech.Walls.gc8r_reinner_pair_nonvacuous G


-- created on 2026-10-23
