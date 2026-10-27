import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc79toporbit.Part4
open Finset StatMech StatMech.Walls


/--
[rc79_mixed_iff_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc79toporbit.lean)
-/
@[path]
private lemma rc79_mixed_iff_ne_eq
  {n : ℕ}
  {b₁ b₂ : Bool} :
-- imply
  (b₁ && b₂, b₁ || b₂) = ((false, true) : Bool × Bool) ↔ b₁ ≠ b₂ := by
-- proof
  apply StatMech.Walls.rc79_mixed_iff_ne b₁ b₂

/--
[rc79_colType_top_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc79toporbit.lean)
-/
@[path]
private lemma rc79_colType_top_iff_eq
  {n : ℕ}
  {p : ConfigSpace (Fin n) × ConfigSpace (Fin n)} :
-- imply
  rc78_colType p = rc79_topType ↔ ∀ i, p.1 i ≠ p.2 i := by
-- proof
  apply StatMech.Walls.rc79_colType_top_iff p

/--
[rc79_colTypeF_diag_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc79toporbit.lean)
-/
@[path]
private lemma rc79_colTypeF_diag_iff_eq
  {n : ℕ}
  {p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)} :
-- imply
  rc78_colTypeF p = rc79_diagTypeF p.1 ↔ p.1 = p.2 := by
-- proof
  apply StatMech.Walls.rc79_colTypeF_diag_iff p

/--
[rc79_occ_self_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc79toporbit.lean)
-/
@[path]
private lemma rc79_occ_self_mem_eq
  {n : ℕ}
  {A : Finset (ConfigSpace (Fin 2))}
  {K : Finset (Fin 2)}
  {w : ConfigSpace (Fin 2)}
-- given
  (h : rc75_occ A K w = true) :
-- imply
  w ∈ A := by
-- proof
  apply StatMech.Walls.rc79_occ_self_mem h

/--
[rc79_disjOcc_mem_both](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc79toporbit.lean)
-/
@[path]
private lemma rc79_disjOcc_mem_both_eq
  {n : ℕ}
  {A B : Finset (ConfigSpace (Fin 2))}
  {w : ConfigSpace (Fin 2)}
-- given
  (h : w ∈ rc75_disjOccF A B) :
-- imply
  w ∈ A ∧ w ∈ B := by
-- proof
  apply StatMech.Walls.rc79_disjOcc_mem_both h

/--
[rc79_diag_orbit_dominates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc79toporbit.lean)
-/
@[path]
private lemma rc79_diag_orbit_dominates_eq
  {n : ℕ}
  {A B : Finset (ConfigSpace (Fin 2))}
  {w : ConfigSpace (Fin 2)} :
-- imply
  rc78_srcOrbit A B (rc79_diagTypeF w) ⊆ rc78_tgtOrbit A B (rc79_diagTypeF w) := by
-- proof
  apply StatMech.Walls.rc79_diag_orbit_dominates A B w

/--
[rc79_diag_orbit_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc79toporbit.lean)
-/
@[path]
private lemma rc79_diag_orbit_card_le_eq
  {n : ℕ}
  {A B : Finset (ConfigSpace (Fin 2))}
  {w : ConfigSpace (Fin 2)} :
-- imply
  (rc78_srcOrbit A B (rc79_diagTypeF w)).card ≤ (rc78_tgtOrbit A B (rc79_diagTypeF w)).card := by
-- proof
  apply StatMech.Walls.rc79_diag_orbit_card_le A B w

/--
[rc79_colTypeF_top_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc79toporbit.lean)
-/
@[path]
private lemma rc79_colTypeF_top_iff_eq
  {n : ℕ}
  {p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)} :
-- imply
  rc78_colTypeF p = rc79_topTypeF ↔ ∀ i, p.1 i ≠ p.2 i := by
-- proof
  apply StatMech.Walls.rc79_colTypeF_top_iff p

/--
[rc79_colTypeF_top_iff_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc79toporbit.lean)
-/
@[path]
private lemma rc79_colTypeF_top_iff_compl_eq
  {n : ℕ}
  {p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)} :
-- imply
  rc78_colTypeF p = rc79_topTypeF ↔ p.2 = rc79_complF p.1 := by
-- proof
  apply StatMech.Walls.rc79_colTypeF_top_iff_compl p

/--
[rc79_srcOrbit_top_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc79toporbit.lean)
-/
@[path]
private lemma rc79_srcOrbit_top_card_eq
  {n : ℕ}
  {A B : Finset (ConfigSpace (Fin 2))} :
-- imply
  (rc78_srcOrbit A B rc79_topTypeF).card = (rc75_disjOccF A B).card := by
-- proof
  apply StatMech.Walls.rc79_srcOrbit_top_card A B

/--
[rc79_tgtOrbit_top_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc79toporbit.lean)
-/
@[path]
private lemma rc79_tgtOrbit_top_card_eq
  {n : ℕ}
  {A B : Finset (ConfigSpace (Fin 2))} :
-- imply
  (rc78_tgtOrbit A B rc79_topTypeF).card = (rc79_reflInterF A B).card := by
-- proof
  apply StatMech.Walls.rc79_tgtOrbit_top_card A B

/--
[rc79_top_orbit_is_wall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc79toporbit.lean)
-/
@[path]
private lemma rc79_top_orbit_is_wall_eq
  {n : ℕ}
  {A B : Finset (ConfigSpace (Fin 2))} :
-- imply
  ((rc78_srcOrbit A B rc79_topTypeF).card ≤ (rc78_tgtOrbit A B rc79_topTypeF).card) ↔ ((rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card) := by
-- proof
  apply StatMech.Walls.rc79_top_orbit_is_wall A B

/--
[rc79_top_wall_rc72_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc79toporbit.lean)
-/
@[path]
private lemma rc79_top_wall_rc72_witness_eq
  {n : ℕ} :
-- imply
  (rc75_disjOccF rc75_wA rc75_wB).card = 2 ∧ (rc79_reflInterF rc75_wA rc75_wB).card = 2 := by
-- proof
  apply StatMech.Walls.rc79_top_wall_rc72_witness

/--
[rc79_top_wall_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc79toporbit.lean)
-/
@[path]
private lemma rc79_top_wall_fin2_eq
  {n : ℕ} :
-- imply
  ∀ A B : Finset (ConfigSpace (Fin 2)), (rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card := by
-- proof
  apply StatMech.Walls.rc79_top_wall_fin2

/--
[rc79_perOrbitDom_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc79toporbit.lean)
-/
@[path]
private lemma rc79_perOrbitDom_fin2_eq
  {n : ℕ} :
-- imply
  ∀ A B : Finset (ConfigSpace (Fin 2)), rc78_PerOrbitDom A B := by
-- proof
  apply StatMech.Walls.rc79_perOrbitDom_fin2

/--
[rc79_split_induction_refuted_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc79toporbit.lean)
-/
@[path]
private lemma rc79_split_induction_refuted_fin3_eq
  {n : ℕ} :
-- imply
  (rc79_disjOcc3 rc79_rA rc79_rB).card = 2 ∧ (rc79_disjOcc2 (rc79_slice2 false rc79_rA) (rc79_slice2 true rc79_rB)).card + (rc79_disjOcc2 (rc79_slice2 true rc79_rA) (rc79_slice2 false rc79_rB)).card = 1 ∧ ¬ (rc79_disjOcc3 rc79_rA rc79_rB).card ≤ (rc79_disjOcc2 (rc79_slice2 false rc79_rA) (rc79_slice2 true rc79_rB)).card + (rc79_disjOcc2 (rc79_slice2 true rc79_rA) (rc79_slice2 false rc79_rB)).card := by
-- proof
  apply StatMech.Walls.rc79_split_induction_refuted_fin3

/--
[rc79_reimerWprobCore_of_boxUnionBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc79toporbit.lean)
-/
@[path]
private lemma rc79_reimerWprobCore_of_boxUnionBound_eq
  {n : ℕ}
-- given
  (h : rc60_BoxUnionBound) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc79_reimerWprobCore_of_boxUnionBound h

/--
[rc79_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc79toporbit.lean)
-/
@[path]
private lemma rc79_status_eq
  {n : ℕ} :
-- imply
  (∀ (A B : Finset (ConfigSpace (Fin 2))) (w : ConfigSpace (Fin 2)), rc78_srcOrbit A B (rc79_diagTypeF w) ⊆ rc78_tgtOrbit A B (rc79_diagTypeF w)) ∧ (∀ A B : Finset (ConfigSpace (Fin 2)), ((rc78_srcOrbit A B rc79_topTypeF).card ≤ (rc78_tgtOrbit A B rc79_topTypeF).card) ↔ ((rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card)) ∧ (∀ A B : Finset (ConfigSpace (Fin 2)), rc78_PerOrbitDom A B) ∧ (∀ A B : Finset (ConfigSpace (Fin 2)), (rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card) ∧ (¬ (rc79_disjOcc3 rc79_rA rc79_rB).card ≤ (rc79_disjOcc2 (rc79_slice2 false rc79_rA) (rc79_slice2 true rc79_rB)).card + (rc79_disjOcc2 (rc79_slice2 true rc79_rA) (rc79_slice2 false rc79_rB)).card) ∧ (rc60_BoxUnionBound → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc79_status


-- created on 2026-10-23
