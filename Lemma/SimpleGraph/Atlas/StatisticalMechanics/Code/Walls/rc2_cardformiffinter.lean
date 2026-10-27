import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc2_cardformiffinter
open Finset StatMech StatMech.Walls


/--
[rc2_interCard_iff_deficit_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_cardformiffinter.lean)
-/
@[path]
private lemma rc2_interCard_iff_deficit_nonpos_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  rc2_boxCard A B ≤ rc2_interCard A B ↔ rc2_deficit A B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc2_interCard_iff_deficit_nonpos A B

/--
[rc2_interCard_eq_complImage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_cardformiffinter.lean)
-/
@[path]
private lemma rc2_interCard_eq_complImage_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  rc2_interCard A B = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∧ (fun a => !ω a) ∈ B)) := by
-- proof
  apply StatMech.Walls.rc2_interCard_eq_complImage A B

/--
[rc2_topSlab_iff_interCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_cardformiffinter.lean)
-/
@[path]
private lemma rc2_topSlab_iff_interCard_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  (#(poc_slabBox A B poc_topKey) ≤ #(poc_slabImg A B poc_topKey)) ↔ rc2_boxCard A B ≤ rc2_interCard A B := by
-- proof
  apply StatMech.Walls.rc2_topSlab_iff_interCard A B

/--
[rc2_topSlab_iff_deficit_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_cardformiffinter.lean)
-/
@[path]
private lemma rc2_topSlab_iff_deficit_nonpos_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  (#(poc_slabBox A B poc_topKey) ≤ #(poc_slabImg A B poc_topKey)) ↔ rc2_deficit A B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc2_topSlab_iff_deficit_nonpos A B

/--
[rc2_reimerCardForm_iff_interCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_cardformiffinter.lean)
-/
@[path]
private lemma rc2_reimerCardForm_iff_interCard_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  StatMech.poc_ReimerCardForm A B ↔ rc2_boxCard A B ≤ rc2_interCard A B := by
-- proof
  apply StatMech.Walls.rc2_reimerCardForm_iff_interCard A B

/--
[rc2_reimerCardForm_iff_deficit_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_cardformiffinter.lean)
-/
@[path]
private lemma rc2_reimerCardForm_iff_deficit_nonpos_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  StatMech.poc_ReimerCardForm A B ↔ rc2_deficit A B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc2_reimerCardForm_iff_deficit_nonpos A B

/--
[rc2_interCard_of_slabCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_cardformiffinter.lean)
-/
@[path]
private lemma rc2_interCard_of_slabCard_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (h : poc_SlabCard A B) :
-- imply
  rc2_boxCard A B ≤ rc2_interCard A B := by
-- proof
  apply StatMech.Walls.rc2_interCard_of_slabCard h

/--
[rc2_deficit_nonpos_of_slabCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_cardformiffinter.lean)
-/
@[path]
private lemma rc2_deficit_nonpos_of_slabCard_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (h : poc_SlabCard A B) :
-- imply
  rc2_deficit A B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc2_deficit_nonpos_of_slabCard h

/--
[rc2_interCard_of_perOrbitCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_cardformiffinter.lean)
-/
@[path]
private lemma rc2_interCard_of_perOrbitCard_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (h : PerOrbitCard A B) :
-- imply
  rc2_boxCard A B ≤ rc2_interCard A B := by
-- proof
  apply StatMech.Walls.rc2_interCard_of_perOrbitCard h

/--
[rc2_interCard_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_cardformiffinter.lean)
-/
@[path]
private lemma rc2_interCard_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc2_boxCard rbi_A rbi_B ≤ rc2_interCard rbi_A rbi_B := by
-- proof
  apply StatMech.Walls.rc2_interCard_rbi

/--
[rc2_deficit_nonpos_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_cardformiffinter.lean)
-/
@[path]
private lemma rc2_deficit_nonpos_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc2_deficit rbi_A rbi_B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc2_deficit_nonpos_rbi

/--
[rc2_interCard_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_cardformiffinter.lean)
-/
@[path]
private lemma rc2_interCard_of_disjoint_support_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S T : Finset α}
-- given
  (hA : DependsOn A (↑S))
  (hB : DependsOn B (↑T))
  (hST : Disjoint S T) :
-- imply
  rc2_boxCard A B ≤ rc2_interCard A B := by
-- proof
  apply StatMech.Walls.rc2_interCard_of_disjoint_support hA hB hST

/--
[rc2_interCard_of_box_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_cardformiffinter.lean)
-/
@[path]
private lemma rc2_interCard_of_box_empty_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hbox : disjointOccurrence A B = ∅) :
-- imply
  rc2_boxCard A B ≤ rc2_interCard A B := by
-- proof
  apply StatMech.Walls.rc2_interCard_of_box_empty hbox


-- created on 2026-10-23
