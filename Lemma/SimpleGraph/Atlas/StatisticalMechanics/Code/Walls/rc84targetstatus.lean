import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc84targetstatus
open MeasureTheory Finset StatMech


/--
[rc84_target_is_genuine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc84targetstatus.lean)
-/
@[path]
private lemma rc84_target_is_genuine_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (h : ReimerWprobCore)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.rc84_target_is_genuine h hp A B

/--
[rc84_minimal_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc84targetstatus.lean)
-/
@[path]
private lemma rc84_minimal_residue_eq
-- given
  (h : rc17_NonMonotoneDeficit) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.rc84_minimal_residue h

/--
[rc84_reimer_of_minimal_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc84targetstatus.lean)
-/
@[path]
private lemma rc84_reimer_of_minimal_residue_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (h : rc17_NonMonotoneDeficit)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.rc84_reimer_of_minimal_residue h hp A B

/--
[rc84_residue_is_famCylBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc84targetstatus.lean)
-/
@[path]
private lemma rc84_residue_is_famCylBox_eq
-- given
  (h : rc20_FamCylBoxResidue) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.rc84_residue_is_famCylBox h

/--
[rc84_what_is_proved](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc84targetstatus.lean)
-/
@[path]
private lemma rc84_what_is_proved_eq :
-- imply
  (∀ {n : ℕ} {A B : Set (ConfigSpace (Fin n))}, (IsIncreasing A ∨ IsDecreasing A) → (IsIncreasing B ∨ IsDecreasing B) → rc5_deficit A B ≤ 0) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 2))), #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) := by
-- proof
  apply StatMech.rc84_what_is_proved

/--
[rc84_off_critical_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc84targetstatus.lean)
-/
@[path]
private lemma rc84_off_critical_path_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (hp : p ≤ 1)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.rc84_off_critical_path hp hA hB

/--
[rc84_target_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc84targetstatus.lean)
-/
@[path]
private lemma rc84_target_status_eq :
-- imply
  (ReimerWprobCore → ∀ {E : Type*} [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)), (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B) ∧ (rc17_NonMonotoneDeficit → ReimerWprobCore) ∧ (∀ {E : Type*} [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) {A B : Set (ConfigSpace E)}, IsIncreasing A → IsIncreasing B → (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 2))), #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) := by
-- proof
  apply StatMech.rc84_target_status


-- created on 2026-10-23
