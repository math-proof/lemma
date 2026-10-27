import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc11reflinterstructure
open Finset StatMech StatMech.Walls


/--
[rc11_mem_reflPull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11reflinterstructure.lean)
-/
@[path]
private lemma rc11_mem_reflPull_eq
  [Fintype α]
  [DecidableEq α]
  {ℬ : Finset (Finset α)}
  {S : Finset α} :
-- imply
  S ∈ rc11_reflPull ℬ ↔ Sᶜ ∈ ℬ := by
-- proof
  apply StatMech.Walls.rc11_mem_reflPull ℬ S

/--
[rc11_isLowerSet_reflPull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11reflinterstructure.lean)
-/
@[path]
private lemma rc11_isLowerSet_reflPull_eq
  [Fintype α]
  [DecidableEq α]
  {ℬ : Finset (Finset α)}
-- given
  (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
-- imply
  IsLowerSet ((rc11_reflPull ℬ : Finset (Finset α)) : Set (Finset α)) := by
-- proof
  apply StatMech.Walls.rc11_isLowerSet_reflPull hℬ

/--
[rc11_isUpperSet_of_isLowerSet_reflPull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11reflinterstructure.lean)
-/
@[path]
private lemma rc11_isUpperSet_of_isLowerSet_reflPull_eq
  [Fintype α]
  [DecidableEq α]
  {ℬ : Finset (Finset α)}
-- given
  (h : IsLowerSet ((rc11_reflPull ℬ : Finset (Finset α)) : Set (Finset α))) :
-- imply
  IsUpperSet (ℬ : Set (Finset α)) := by
-- proof
  apply StatMech.Walls.rc11_isUpperSet_of_isLowerSet_reflPull h

/--
[rc11_reflInter_eq_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11reflinterstructure.lean)
-/
@[path]
private lemma rc11_reflInter_eq_inter_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc10_reflInter 𝒜 ℬ = 𝒜 ∩ rc11_reflPull ℬ := by
-- proof
  apply StatMech.Walls.rc11_reflInter_eq_inter 𝒜 ℬ

/--
[rc11_reflInter_isUpperMeetDown](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11reflinterstructure.lean)
-/
@[path]
private lemma rc11_reflInter_isUpperMeetDown_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
  (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
-- imply
  ∃ rℬ : Finset (Finset α), IsUpperSet (𝒜 : Set (Finset α)) ∧ IsLowerSet (rℬ : Set (Finset α)) ∧ rc10_reflInter 𝒜 ℬ = 𝒜 ∩ rℬ := by
-- proof
  apply StatMech.Walls.rc11_reflInter_isUpperMeetDown h𝒜 hℬ

/--
[rc11_reflPull_reflPull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11reflinterstructure.lean)
-/
@[path]
private lemma rc11_reflPull_reflPull_eq
  [Fintype α]
  [DecidableEq α]
  {ℬ : Finset (Finset α)} :
-- imply
  rc11_reflPull (rc11_reflPull ℬ) = ℬ := by
-- proof
  apply StatMech.Walls.rc11_reflPull_reflPull ℬ

/--
[rc11_reflPull_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11reflinterstructure.lean)
-/
@[path]
private lemma rc11_reflPull_univ_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc11_reflPull (univ : Finset (Finset α)) = univ := by
-- proof
  apply StatMech.Walls.rc11_reflPull_univ

/--
[rc11_reflInter_univ_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11reflinterstructure.lean)
-/
@[path]
private lemma rc11_reflInter_univ_univ_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc10_reflInter (univ : Finset (Finset α)) univ = univ := by
-- proof
  apply StatMech.Walls.rc11_reflInter_univ_univ

/--
[rc11_card_reflInter_eq_card_upperMeetDown](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11reflinterstructure.lean)
-/
@[path]
private lemma rc11_card_reflInter_eq_card_upperMeetDown_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
-- imply
  #(rc10_reflInter 𝒜 ℬ) = #(𝒜 ∩ rc11_reflPull ℬ) ∧ IsLowerSet ((rc11_reflPull ℬ : Finset (Finset α)) : Set (Finset α)) := by
-- proof
  apply StatMech.Walls.rc11_card_reflInter_eq_card_upperMeetDown hℬ


-- created on 2026-10-23
