import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc6hallavailable.Part2
open Finset Function StatMech StatMech.Walls


/--
[rc6_mem_boxFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6hallavailable.lean)
-/
@[path]
private lemma rc6_mem_boxFinset_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {ω : ConfigSpace α} :
-- imply
  ω ∈ rc6_boxFinset A B ↔ ω ∈ disjointOccurrence A B := by
-- proof
  apply StatMech.Walls.rc6_mem_boxFinset

/--
[rc6_mem_imgFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6hallavailable.lean)
-/
@[path]
private lemma rc6_mem_imgFinset_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {ω : ConfigSpace α} :
-- imply
  ω ∈ rc6_imgFinset A B ↔ (ω ∈ A ∧ (fun a => !ω a) ∈ B) := by
-- proof
  apply StatMech.Walls.rc6_mem_imgFinset

/--
[rc6_reimerCardForm_iff_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6hallavailable.lean)
-/
@[path]
private lemma rc6_reimerCardForm_iff_card_le_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  poc_ReimerCardForm A B ↔ #(rc6_boxFinset A B) ≤ #(rc6_imgFinset A B) := by
-- proof
  apply StatMech.Walls.rc6_reimerCardForm_iff_card_le A B

/--
[rc6_card_le_iff_embedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6hallavailable.lean)
-/
@[path]
private lemma rc6_card_le_iff_embedding_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  #(rc6_boxFinset A B) ≤ #(rc6_imgFinset A B) ↔ Nonempty (↥(rc6_boxFinset A B) ↪ ↥(rc6_imgFinset A B)) := by
-- proof
  apply StatMech.Walls.rc6_card_le_iff_embedding A B

/--
[rc6_reimerCardForm_iff_embedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6hallavailable.lean)
-/
@[path]
private lemma rc6_reimerCardForm_iff_embedding_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  poc_ReimerCardForm A B ↔ Nonempty (↥(rc6_boxFinset A B) ↪ ↥(rc6_imgFinset A B)) := by
-- proof
  apply StatMech.Walls.rc6_reimerCardForm_iff_embedding A B

/--
[rc6_fullRel_nbhd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6hallavailable.lean)
-/
@[path]
private lemma rc6_fullRel_nbhd_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {Aset : Finset (↥(rc6_boxFinset A B))}
-- given
  (hne : Aset.Nonempty) :
-- imply
  (Finset.univ.filter (fun b : ↥(rc6_imgFinset A B) => ∃ a ∈ Aset, rc6_fullRel A B a b)) = Finset.univ := by
-- proof
  apply StatMech.Walls.rc6_fullRel_nbhd A B Aset hne

/--
[rc6_hallCond_iff_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6hallavailable.lean)
-/
@[path]
private lemma rc6_hallCond_iff_card_le_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  (∀ Aset : Finset (↥(rc6_boxFinset A B)), #Aset ≤ #{b | ∃ a ∈ Aset, rc6_fullRel A B a b}) ↔ #(rc6_boxFinset A B) ≤ #(rc6_imgFinset A B) := by
-- proof
  apply StatMech.Walls.rc6_hallCond_iff_card_le A B

/--
[rc6_hall_transversal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6hallavailable.lean)
-/
@[path]
private lemma rc6_hall_transversal_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hle : #(rc6_boxFinset A B) ≤ #(rc6_imgFinset A B)) :
-- imply
  ∃ f : ↥(rc6_boxFinset A B) → ↥(rc6_imgFinset A B), Injective f ∧ ∀ x, rc6_fullRel A B x (f x) := by
-- proof
  apply StatMech.Walls.rc6_hall_transversal A B hle

/--
[rc6_hall_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6hallavailable.lean)
-/
@[path]
private lemma rc6_hall_injection_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hle : #(rc6_boxFinset A B) ≤ #(rc6_imgFinset A B)) :
-- imply
  Nonempty (↥(rc6_boxFinset A B) ↪ ↥(rc6_imgFinset A B)) := by
-- proof
  apply StatMech.Walls.rc6_hall_injection A B hle

/--
[rc6_box_to_img_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6hallavailable.lean)
-/
@[path]
private lemma rc6_box_to_img_injection_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hle : #(rc6_boxFinset A B) ≤ #(rc6_imgFinset A B)) :
-- imply
  ∃ f : ConfigSpace α → ConfigSpace α, Set.InjOn f (disjointOccurrence A B) ∧ Set.MapsTo f (disjointOccurrence A B) {ω | ω ∈ A ∧ (fun a => !ω a) ∈ B} := by
-- proof
  apply StatMech.Walls.rc6_box_to_img_injection A B hle

/--
[rc6_reimerCardFormAll_iff_embeddingAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6hallavailable.lean)
-/
@[path]
private lemma rc6_reimerCardFormAll_iff_embeddingAll_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ReimerCardFormAll ↔ ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), Nonempty (↥(rc6_boxFinset A B) ↪ ↥(rc6_imgFinset A B)) := by
-- proof
  apply StatMech.Walls.rc6_reimerCardFormAll_iff_embeddingAll

/--
[rc6_embedding_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6hallavailable.lean)
-/
@[path]
private lemma rc6_embedding_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  Nonempty (↥(rc6_boxFinset rbi_A rbi_B) ↪ ↥(rc6_imgFinset rbi_A rbi_B)) := by
-- proof
  apply StatMech.Walls.rc6_embedding_rbi

/--
[rc6_embedding_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6hallavailable.lean)
-/
@[path]
private lemma rc6_embedding_of_disjoint_support_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S T : Finset α}
-- given
  (hA : DependsOn A (↑S))
  (hB : DependsOn B (↑T))
  (hST : Disjoint S T) :
-- imply
  Nonempty (↥(rc6_boxFinset A B) ↪ ↥(rc6_imgFinset A B)) := by
-- proof
  apply StatMech.Walls.rc6_embedding_of_disjoint_support hA hB hST

/--
[rc6_embedding_of_box_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6hallavailable.lean)
-/
@[path]
private lemma rc6_embedding_of_box_empty_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hbox : disjointOccurrence A B = ∅) :
-- imply
  Nonempty (↥(rc6_boxFinset A B) ↪ ↥(rc6_imgFinset A B)) := by
-- proof
  apply StatMech.Walls.rc6_embedding_of_box_empty hbox

/--
[rc6_embedding_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6hallavailable.lean)
-/
@[path]
private lemma rc6_embedding_one_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace (Fin 1))} :
-- imply
  Nonempty (↥(rc6_boxFinset A B) ↪ ↥(rc6_imgFinset A B)) := by
-- proof
  apply StatMech.Walls.rc6_embedding_one A B

/--
[rc6_hall_available](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6hallavailable.lean)
-/
@[path]
private lemma rc6_hall_available_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  (poc_ReimerCardForm A B ↔ Nonempty (↥(rc6_boxFinset A B) ↪ ↥(rc6_imgFinset A B))) ∧ ((∀ Aset : Finset (↥(rc6_boxFinset A B)), #Aset ≤ #{b | ∃ a ∈ Aset, rc6_fullRel A B a b}) ↔ #(rc6_boxFinset A B) ≤ #(rc6_imgFinset A B)) := by
-- proof
  apply StatMech.Walls.rc6_hall_available A B


-- created on 2026-10-23
