import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc78hallmarriage
open Finset StatMech StatMech.Walls


/--
[rc78_swapAt_colType](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc78hallmarriage.lean)
-/
@[path]
private lemma rc78_swapAt_colType_eq
  {n : ℕ}
  {i : Fin n}
  {p : ConfigSpace (Fin n) × ConfigSpace (Fin n)} :
-- imply
  rc78_colType (swapAt i p) = rc78_colType p := by
-- proof
  apply StatMech.Walls.rc78_swapAt_colType i p

/--
[rc78_swapAtF_colType](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc78hallmarriage.lean)
-/
@[path]
private lemma rc78_swapAtF_colType_eq
  {n : ℕ}
  {i : Fin 2}
  {p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)} :
-- imply
  rc78_colTypeF (rc75_swapAtF i p) = rc78_colTypeF p := by
-- proof
  apply StatMech.Walls.rc78_swapAtF_colType i p

/--
[rc78_nbhd_eq_tgtOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc78hallmarriage.lean)
-/
@[path]
private lemma rc78_nbhd_eq_tgtOrbit_eq
  {n : ℕ}
  {A B : Finset (ConfigSpace (Fin 2))}
  {p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)} :
-- imply
  rc78_nbhd A B p = rc78_tgtOrbit A B (rc78_colTypeF p) := by
-- proof
  apply StatMech.Walls.rc78_nbhd_eq_tgtOrbit A B p

/--
[rc78_filter_subset_srcOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc78hallmarriage.lean)
-/
@[path]
private lemma rc78_filter_subset_srcOrbit_eq
  {n : ℕ}
  {A B : Finset (ConfigSpace (Fin 2))}
  {𝒯 : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2))}
  {t : Fin 2 → Bool × Bool}
-- given
  (h𝒯 : 𝒯 ⊆ rc75_sourceF A B) :
-- imply
  (𝒯.filter (fun p => rc78_colTypeF p = t)) ⊆ rc78_srcOrbit A B t := by
-- proof
  apply StatMech.Walls.rc78_filter_subset_srcOrbit A B h𝒯 t

/--
[rc78_biUnion_nbhd_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc78hallmarriage.lean)
-/
@[path]
private lemma rc78_biUnion_nbhd_eq_eq
  {n : ℕ}
  {A B : Finset (ConfigSpace (Fin 2))}
  {𝒯 : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2))} :
-- imply
  𝒯.biUnion (rc78_nbhd A B) = (𝒯.image rc78_colTypeF).biUnion (rc78_tgtOrbit A B) := by
-- proof
  apply StatMech.Walls.rc78_biUnion_nbhd_eq A B 𝒯

/--
[rc78_marriage_of_perOrbitDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc78hallmarriage.lean)
-/
@[path]
private lemma rc78_marriage_of_perOrbitDom_eq
  {n : ℕ}
  {A B : Finset (ConfigSpace (Fin 2))}
-- given
  (h : rc78_PerOrbitDom A B) :
-- imply
  rc78_Marriage A B := by
-- proof
  apply StatMech.Walls.rc78_marriage_of_perOrbitDom A B h

/--
[rc78_existsInjective_of_marriage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc78hallmarriage.lean)
-/
@[path]
private lemma rc78_existsInjective_of_marriage_eq
  {n : ℕ}
  {A B : Finset (ConfigSpace (Fin 2))}
-- given
  (h : rc78_Marriage A B) :
-- imply
  ∃ f : (rc75_sourceF A B) → (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)), Function.Injective f ∧ ∀ p : (rc75_sourceF A B), f p ∈ rc78_nbhd A B (p : _) := by
-- proof
  apply StatMech.Walls.rc78_existsInjective_of_marriage A B h

/--
[rc78_existsInjective_of_perOrbitDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc78hallmarriage.lean)
-/
@[path]
private lemma rc78_existsInjective_of_perOrbitDom_eq
  {n : ℕ}
  {A B : Finset (ConfigSpace (Fin 2))}
-- given
  (h : rc78_PerOrbitDom A B) :
-- imply
  ∃ f : (rc75_sourceF A B) → (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)), Function.Injective f ∧ ∀ p : (rc75_sourceF A B), f p ∈ rc78_nbhd A B (p : _) := by
-- proof
  apply StatMech.Walls.rc78_existsInjective_of_perOrbitDom A B h

/--
[rc78_count_of_existsInjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc78hallmarriage.lean)
-/
@[path]
private lemma rc78_count_of_existsInjective_eq
  {n : ℕ}
  {A B : Finset (ConfigSpace (Fin 2))}
-- given
  (hplan : ∃ f : (rc75_sourceF A B) → (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)), Function.Injective f ∧ ∀ p : (rc75_sourceF A B), f p ∈ rc78_nbhd A B (p : _)) :
-- imply
  2 ^ 2 * (rc75_disjOccF A B).card ≤ A.card * B.card := by
-- proof
  apply StatMech.Walls.rc78_count_of_existsInjective A B hplan

/--
[rc78_perOrbitDom_rc72_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc78hallmarriage.lean)
-/
@[path]
private lemma rc78_perOrbitDom_rc72_witness_eq
  {n : ℕ} :
-- imply
  rc78_PerOrbitDom rc75_wA rc75_wB := by
-- proof
  apply StatMech.Walls.rc78_perOrbitDom_rc72_witness

/--
[rc78_perOrbitDom_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc78hallmarriage.lean)
-/
@[path]
private lemma rc78_perOrbitDom_fin2_eq
  {n : ℕ} :
-- imply
  ∀ A B : Finset (ConfigSpace (Fin 2)), rc78_PerOrbitDom A B := by
-- proof
  apply StatMech.Walls.rc78_perOrbitDom_fin2

/--
[rc78_topOrbit_card_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc78hallmarriage.lean)
-/
@[path]
private lemma rc78_topOrbit_card_fin2_eq
  {n : ℕ} :
-- imply
  (rc78_srcOrbit rc75_wA rc75_wB (fun _ => (false, true))).card = 2 ∧ (rc78_tgtOrbit rc75_wA rc75_wB (fun _ => (false, true))).card = 2 := by
-- proof
  apply StatMech.Walls.rc78_topOrbit_card_fin2

/--
[rc78_not_left_regular_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc78hallmarriage.lean)
-/
@[path]
private lemma rc78_not_left_regular_fin2_eq
  {n : ℕ} :
-- imply
  ∃ p ∈ rc75_sourceF rc75_wA rc75_wB, ∃ q ∈ rc75_sourceF rc75_wA rc75_wB, rc78_leftDeg rc75_wA rc75_wB p ≠ rc78_leftDeg rc75_wA rc75_wB q := by
-- proof
  apply StatMech.Walls.rc78_not_left_regular_fin2

/--
[rc78_reimerWprobCore_of_boxUnionBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc78hallmarriage.lean)
-/
@[path]
private lemma rc78_reimerWprobCore_of_boxUnionBound_eq
  {n : ℕ}
-- given
  (h : rc60_BoxUnionBound) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc78_reimerWprobCore_of_boxUnionBound h

/--
[rc78_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc78hallmarriage.lean)
-/
@[path]
private lemma rc78_status_eq
  {n : ℕ} :
-- imply
  (∀ (m : ℕ) (i : Fin m) (p : ConfigSpace (Fin m) × ConfigSpace (Fin m)), rc78_colType (swapAt i p) = rc78_colType p) ∧ (∀ A B : Finset (ConfigSpace (Fin 2)), rc78_PerOrbitDom A B → ∃ f : (rc75_sourceF A B) → (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)), Function.Injective f ∧ ∀ p : (rc75_sourceF A B), f p ∈ rc78_nbhd A B (p : _)) ∧ (∀ A B : Finset (ConfigSpace (Fin 2)), (∃ f : (rc75_sourceF A B) → (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)), Function.Injective f ∧ ∀ p : (rc75_sourceF A B), f p ∈ rc78_nbhd A B (p : _)) → 2 ^ 2 * (rc75_disjOccF A B).card ≤ A.card * B.card) ∧ (rc78_PerOrbitDom rc75_wA rc75_wB) ∧ (∃ p ∈ rc75_sourceF rc75_wA rc75_wB, ∃ q ∈ rc75_sourceF rc75_wA rc75_wB, rc78_leftDeg rc75_wA rc75_wB p ≠ rc78_leftDeg rc75_wA rc75_wB q) ∧ (rc60_BoxUnionBound → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc78_status


-- created on 2026-10-23
