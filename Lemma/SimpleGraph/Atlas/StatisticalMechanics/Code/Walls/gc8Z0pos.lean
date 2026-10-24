import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc8Z0pos
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc8_Z0_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8Z0pos.lean)
-/
@[path]
private lemma gc8_Z0_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 (Option V) → ℝ} :
-- imply
  0 < Sharpness.currentSum (withGhost G) β J ∅ := by
-- proof
  apply StatMech.Walls.gc8_Z0_pos G β J

/--
[gc8_Z0_pos_ghost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8Z0pos.lean)
-/
@[path]
private lemma gc8_Z0_pos_ghost_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h : ℝ) :
-- imply
  0 < Sharpness.currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ := by
-- proof
  apply StatMech.Walls.gc8_Z0_pos_ghost G β h

/--
[gc8_Z0_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8Z0pos.lean)
-/
@[path]
private lemma gc8_Z0_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 (Option V) → ℝ} :
-- imply
  Sharpness.currentSum (withGhost G) β J ∅ ≠ 0 := by
-- proof
  apply StatMech.Walls.gc8_Z0_ne_zero G β J

/--
[gc8_Z0_ne_zero_ghost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8Z0pos.lean)
-/
@[path]
private lemma gc8_Z0_ne_zero_ghost_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h : ℝ) :
-- imply
  Sharpness.currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ ≠ 0 := by
-- proof
  apply StatMech.Walls.gc8_Z0_ne_zero_ghost G β h

/--
[gc8_Z0_eq_partition_over_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8Z0pos.lean)
-/
@[path]
private lemma gc8_Z0_eq_partition_over_pow_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 (Option V) → ℝ} :
-- imply
  Sharpness.currentSum (withGhost G) β J ∅ = Sharpness.partitionJ (withGhost G) β J / (2 : ℝ) ^ (Fintype.card (Option V)) := by
-- proof
  apply StatMech.Walls.gc8_Z0_eq_partition_over_pow G β J

/--
[gc8_ghostRatio_well_defined](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8Z0pos.lean)
-/
@[path]
private lemma gc8_ghostRatio_well_defined_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a : V}
-- given
  (β h : ℝ) :
-- imply
  isingExpectation G β h (fun s => spin s a) = Sharpness.currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({a} : Finset V).map someEmb)) / Sharpness.currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ ∧ 0 < Sharpness.currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ := by
-- proof
  apply StatMech.Walls.gc8_ghostRatio_well_defined G β h a

/--
[gc8_eq15_insertion_ghost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8Z0pos.lean)
-/
@[path]
private lemma gc8_eq15_insertion_ghost_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 (Option V) → ℝ}
  {A : Finset (Option V)} :
-- imply
  Sharpness.currentSum (withGhost G) β J A = Sharpness.expectationJ (withGhost G) β J A * Sharpness.currentSum (withGhost G) β J ∅ := by
-- proof
  apply StatMech.Walls.gc8_eq15_insertion_ghost G β J A

/--
[gc8_claim1_griffiths_step_ghost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8Z0pos.lean)
-/
@[path]
private lemma gc8_claim1_griffiths_step_ghost_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 (Option V) → ℝ}
  {A : Finset (Option V)}
  {eΛ : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hgriff : Sharpness.expectationJ (withGhost G) β J A ≤ eΛ) :
-- imply
  eΛ * Sharpness.currentSum (withGhost G) β J A ≥ (Sharpness.expectationJ (withGhost G) β J A) ^ 2 * Sharpness.currentSum (withGhost G) β J ∅ := by
-- proof
  apply StatMech.Walls.gc8_claim1_griffiths_step_ghost G β J A eΛ hβ hJ hgriff

/--
[gc8_u3_nonpos_of_eqSwi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8Z0pos.lean)
-/
@[path]
private lemma gc8_u3_nonpos_of_eqSwi_eq
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
  (hid : gc6_EqSwiIdentity G β h o) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc8_u3_nonpos_of_eqSwi G β h hβ hh o hid x y

/--
[gc8_Z0_pos_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8Z0pos.lean)
-/
@[path]
private lemma gc8_Z0_pos_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  0 < Sharpness.currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) ∅ := by
-- proof
  apply StatMech.Walls.gc8_Z0_pos_nonvacuous G

/--
[gc8_ghostRatio_well_defined_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8Z0pos.lean)
-/
@[path]
private lemma gc8_ghostRatio_well_defined_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (fun s => spin s 0) = Sharpness.currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) (insert (none : Option (Fin 3)) (({0} : Finset (Fin 3)).map someEmb)) / Sharpness.currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) ∅ ∧ 0 < Sharpness.currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) ∅ := by
-- proof
  apply StatMech.Walls.gc8_ghostRatio_well_defined_nonvacuous G


-- created on 2026-10-23
