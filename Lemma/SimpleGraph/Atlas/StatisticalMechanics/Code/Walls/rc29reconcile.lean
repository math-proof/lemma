import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc29reconcile.Part2
open Finset StatMech StatMech.Walls


/--
[rc29_toggle_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc29reconcile.lean)
-/
@[path]
private lemma rc29_toggle_involutive_eq
  [Fintype α]
  [DecidableEq α]
  {a : α}
  {S : Finset α} :
-- imply
  (if a ∈ (if a ∈ S then S.erase a else insert a S) then (if a ∈ S then S.erase a else insert a S).erase a else insert a (if a ∈ S then S.erase a else insert a S)) = S := by
-- proof
  apply StatMech.Walls.rc29_toggle_involutive a S

/--
[rc29_mem_flipA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc29reconcile.lean)
-/
@[path]
private lemma rc29_mem_flipA_eq
  [Fintype α]
  [DecidableEq α]
  {a : α}
  {ℬ : Finset (Finset α)}
  {S : Finset α} :
-- imply
  S ∈ rc29_flipA a ℬ ↔ (if a ∈ S then S.erase a else insert a S) ∈ ℬ := by
-- proof
  apply StatMech.Walls.rc29_mem_flipA a ℬ S

/--
[rc29_flipA_nonMemberSubfamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc29reconcile.lean)
-/
@[path]
private lemma rc29_flipA_nonMemberSubfamily_eq
  [Fintype α]
  [DecidableEq α]
  {a : α}
  {ℬ : Finset (Finset α)} :
-- imply
  (rc29_flipA a ℬ).nonMemberSubfamily a = ℬ.memberSubfamily a := by
-- proof
  apply StatMech.Walls.rc29_flipA_nonMemberSubfamily a ℬ

/--
[rc29_flipA_memberSubfamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc29reconcile.lean)
-/
@[path]
private lemma rc29_flipA_memberSubfamily_eq
  [Fintype α]
  [DecidableEq α]
  {a : α}
  {ℬ : Finset (Finset α)} :
-- imply
  (rc29_flipA a ℬ).memberSubfamily a = ℬ.nonMemberSubfamily a := by
-- proof
  apply StatMech.Walls.rc29_flipA_memberSubfamily a ℬ

/--
[rc29_flippedBox_crossRecursion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc29reconcile.lean)
-/
@[path]
private lemma rc29_flippedBox_crossRecursion_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 ℬ : Finset (Finset α)}
  {a : α}
-- given
  (haE : a ∈ E) :
-- imply
  #(rc28_famCylBoxE E 𝒜 (rc29_flipA a ℬ)) ≤ #(rc28_famCylBoxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a)) + #(rc28_famCylBoxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a)) := by
-- proof
  apply StatMech.Walls.rc29_flippedBox_crossRecursion 𝒜 ℬ haE

/--
[rc29_flippedReflE_sameSideRecursion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc29reconcile.lean)
-/
@[path]
private lemma rc29_flippedReflE_sameSideRecursion_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 ℬ : Finset (Finset α)}
  {a : α}
-- given
  (haE : a ∈ E) :
-- imply
  #(rc14_reflE E 𝒜 (rc29_flipA a ℬ)) = #(rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a)) + #(rc14_reflE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a)) := by
-- proof
  apply StatMech.Walls.rc29_flippedReflE_sameSideRecursion 𝒜 ℬ haE

/--
[rc29_box_le_flippedReflE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc29reconcile.lean)
-/
@[path]
private lemma rc29_box_le_flippedReflE_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 ℬ : Finset (Finset α)}
  {a : α}
-- given
  (haE : a ∈ E)
  (hwnn : #(rc28_famCylBoxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a)) ≤ #(rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a)))
  (hwmm : #(rc28_famCylBoxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a)) ≤ #(rc14_reflE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a))) :
-- imply
  #(rc28_famCylBoxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 (rc29_flipA a ℬ)) := by
-- proof
  apply StatMech.Walls.rc29_box_le_flippedReflE 𝒜 ℬ haE hwnn hwmm

/--
[rc29_flipCandidate_of_wall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc29reconcile.lean)
-/
@[path]
private lemma rc29_flipCandidate_of_wall_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 ℬ : Finset (Finset α)}
  {a : α}
-- given
  (hwall : ∀ (E : Finset α) (𝒜 ℬ : Finset (Finset α)), #(rc28_famCylBoxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 ℬ))
  (haE : a ∈ E) :
-- imply
  #(rc28_famCylBoxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 (rc29_flipA a ℬ)) := by
-- proof
  apply StatMech.Walls.rc29_flipCandidate_of_wall hwall 𝒜 ℬ haE

/--
[rc29_flipAComp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc29reconcile.lean)
-/
@[path]
private lemma rc29_flipAComp_eq_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {a : Fin n}
  {ℬ : Finset (Finset (Fin n))} :
-- imply
  rc29_flipAComp n a ℬ = rc29_flipA a ℬ := by
-- proof
  apply StatMech.Walls.rc29_flipAComp_eq n a ℬ

/--
[rc29_box_flip_strictDecrease](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc29reconcile.lean)
-/
@[path]
private lemma rc29_box_flip_strictDecrease_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc28_famCylBoxE (univ : Finset (Fin 3)) ({∅, {0}, {1}}) ({∅, {0}, {0, 1}, {2}, {0, 2}, {0, 1, 2}})) > #(rc28_famCylBoxE (univ : Finset (Fin 3)) ({∅, {0}, {1}}) (rc29_flipA 0 ({∅, {0}, {0, 1}, {2}, {0, 2}, {0, 1, 2}} : Finset (Finset (Fin 3))))) := by
-- proof
  apply StatMech.Walls.rc29_box_flip_strictDecrease

/--
[rc29_flipCandidate_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc29reconcile.lean)
-/
@[path]
private lemma rc29_flipCandidate_witness_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc28_famCylBoxE (univ : Finset (Fin 3)) ({∅, {0}, {1}, {2}, {0, 1}}) ({∅, {0}, {1}, {0, 1}, {0, 2}})) ≤ #(rc14_reflE (univ : Finset (Fin 3)) ({∅, {0}, {1}, {2}, {0, 1}}) (rc29_flipA 0 ({∅, {0}, {1}, {0, 1}, {0, 2}} : Finset (Finset (Fin 3))))) := by
-- proof
  apply StatMech.Walls.rc29_flipCandidate_witness

/--
[rc29_famCylBox_le_reflInter_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc29reconcile.lean)
-/
@[path]
private lemma rc29_famCylBox_le_reflInter_flip_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {a : α}
-- given
  (hwall : ∀ (E : Finset α) (𝒜 ℬ : Finset (Finset α)), #(rc28_famCylBoxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 ℬ)) :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 (rc29_flipA a ℬ)) := by
-- proof
  apply StatMech.Walls.rc29_famCylBox_le_reflInter_flip hwall 𝒜 ℬ a

/--
[rc29_toggle_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc29reconcile.lean)
-/
@[path]
private lemma rc29_toggle_compl_eq
  [Fintype α]
  [DecidableEq α]
  {a : α}
  {S : Finset α} :
-- imply
  (if a ∈ S then S.erase a else insert a S)ᶜ = (if a ∈ Sᶜ then Sᶜ.erase a else insert a Sᶜ) := by
-- proof
  apply StatMech.Walls.rc29_toggle_compl a S

/--
[rc29_reflInter_doubleFlip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc29reconcile.lean)
-/
@[path]
private lemma rc29_reflInter_doubleFlip_eq
  [Fintype α]
  [DecidableEq α]
  {a : α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  #(rc10_reflInter (rc29_flipA a 𝒜) (rc29_flipA a ℬ)) = #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc29_reflInter_doubleFlip a 𝒜 ℬ


-- created on 2026-10-23
