import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rmr_topkey.Part2
open Finset StatMech StatMech.Walls


/--
[topFlip_eq_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_topkey.lean)
-/
@[path]
private lemma topFlip_eq_compl_eq
  [Fintype α]
  [DecidableEq α]
  {ω : ConfigSpace α} :
-- imply
  poc_keyFlip (poc_topKey : ConfigSpace α × ConfigSpace α) ω = fun a => !ω a := by
-- proof
  apply StatMech.Walls.topFlip_eq_compl ω

/--
[topKey_slab_isWholeCube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_topkey.lean)
-/
@[path]
private lemma topKey_slab_isWholeCube_eq
  [Fintype α]
  [DecidableEq α]
  {ω : ConfigSpace α} :
-- imply
  orbitKey (ω, poc_keyFlip (poc_topKey : ConfigSpace α × ConfigSpace α) ω) = poc_topKey := by
-- proof
  apply StatMech.Walls.topKey_slab_isWholeCube ω

/--
[topKey_slabBox_eq_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_topkey.lean)
-/
@[path]
private lemma topKey_slabBox_eq_box_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  poc_slabBox A B poc_topKey = Finset.univ.filter (fun ω => ω ∈ disjointOccurrence A B) := by
-- proof
  apply StatMech.Walls.topKey_slabBox_eq_box A B

/--
[topKey_slabImg_eq_complImage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_topkey.lean)
-/
@[path]
private lemma topKey_slabImg_eq_complImage_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  poc_slabImg A B poc_topKey = Finset.univ.filter (fun ω => ω ∈ A ∧ (fun a => !ω a) ∈ B) := by
-- proof
  apply StatMech.Walls.topKey_slabImg_eq_complImage A B

/--
[topKey_slabCard_eq_reimerCardForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_topkey.lean)
-/
@[path]
private lemma topKey_slabCard_eq_reimerCardForm_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  (#(poc_slabBox A B poc_topKey) ≤ #(poc_slabImg A B poc_topKey)) ↔ ReimerCardForm A B := by
-- proof
  apply StatMech.Walls.topKey_slabCard_eq_reimerCardForm A B

/--
[reimerCardForm_of_slabCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_topkey.lean)
-/
@[path]
private lemma reimerCardForm_of_slabCard_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (h : poc_SlabCard A B) :
-- imply
  ReimerCardForm A B := by
-- proof
  apply StatMech.Walls.reimerCardForm_of_slabCard h

/--
[reimerCardForm_of_perOrbitCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_topkey.lean)
-/
@[path]
private lemma reimerCardForm_of_perOrbitCard_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (h : PerOrbitCard A B) :
-- imply
  ReimerCardForm A B := by
-- proof
  apply StatMech.Walls.reimerCardForm_of_perOrbitCard h

/--
[reimerCardForm_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_topkey.lean)
-/
@[path]
private lemma reimerCardForm_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ReimerCardForm rbi_A rbi_B := by
-- proof
  apply StatMech.Walls.reimerCardForm_rbi

/--
[reimerCardForm_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_topkey.lean)
-/
@[path]
private lemma reimerCardForm_of_disjoint_support_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S T : Finset α}
-- given
  (hA : DependsOn A (↑S))
  (hB : DependsOn B (↑T))
  (hST : Disjoint S T) :
-- imply
  ReimerCardForm A B := by
-- proof
  apply StatMech.Walls.reimerCardForm_of_disjoint_support hA hB hST

/--
[reimerCardForm_of_box_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_topkey.lean)
-/
@[path]
private lemma reimerCardForm_of_box_empty_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hbox : disjointOccurrence A B = ∅) :
-- imply
  ReimerCardForm A B := by
-- proof
  apply StatMech.Walls.reimerCardForm_of_box_empty hbox


-- created on 2026-10-23
