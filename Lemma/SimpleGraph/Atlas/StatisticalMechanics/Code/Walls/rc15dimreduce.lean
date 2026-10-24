import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc15dimreduce
open Finset StatMech StatMech.Walls


/--
[rc15_reflE_mem_erase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc15dimreduce.lean)
-/
@[path]
private lemma rc15_reflE_mem_erase_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 ℬ : Finset (Finset α)}
  {a : α}
  {S : Finset α}
-- given
  (haE : a ∈ E)
  (haS : a ∈ S) :
-- imply
  S.erase a ∈ rc14_reflE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a) ↔ S ∈ rc14_reflE E 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc15_reflE_mem_erase E 𝒜 ℬ a S haE haS

/--
[rc15_reflE_mem_id](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc15dimreduce.lean)
-/
@[path]
private lemma rc15_reflE_mem_id_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 ℬ : Finset (Finset α)}
  {a : α}
  {S : Finset α}
-- given
  (haE : a ∈ E)
  (haS : a ∉ S) :
-- imply
  S ∈ rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a) ↔ S ∈ rc14_reflE E 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc15_reflE_mem_id E 𝒜 ℬ a S haE haS

/--
[rc15_card_reflE_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc15dimreduce.lean)
-/
@[path]
private lemma rc15_card_reflE_slice_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 ℬ : Finset (Finset α)}
  {a : α}
-- given
  (haE : a ∈ E) :
-- imply
  #(rc14_reflE E 𝒜 ℬ) = #(rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a)) + #(rc14_reflE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a)) := by
-- proof
  apply StatMech.Walls.rc15_card_reflE_slice E 𝒜 ℬ a haE

/--
[rc15_upperOn_univ_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc15dimreduce.lean)
-/
@[path]
private lemma rc15_upperOn_univ_iff_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 : Finset (Finset α)} :
-- imply
  rc15_UpperOn univ 𝒜 ↔ IsUpperSet (𝒜 : Set (Finset α)) := by
-- proof
  apply StatMech.Walls.rc15_upperOn_univ_iff 𝒜

/--
[rc15_upperOn_nonMember](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc15dimreduce.lean)
-/
@[path]
private lemma rc15_upperOn_nonMember_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 : Finset (Finset α)}
  {a : α}
-- given
  (h𝒜 : rc15_UpperOn E 𝒜) :
-- imply
  rc15_UpperOn (E.erase a) (𝒜.nonMemberSubfamily a) := by
-- proof
  apply StatMech.Walls.rc15_upperOn_nonMember h𝒜 a

/--
[rc15_upperOn_member](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc15dimreduce.lean)
-/
@[path]
private lemma rc15_upperOn_member_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 : Finset (Finset α)}
  {a : α}
-- given
  (h𝒜 : rc15_UpperOn E 𝒜)
  (haE : a ∈ E) :
-- imply
  rc15_UpperOn (E.erase a) (𝒜.memberSubfamily a) := by
-- proof
  apply StatMech.Walls.rc15_upperOn_member h𝒜 a haE

/--
[rc15_mem_member_of_nonMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc15dimreduce.lean)
-/
@[path]
private lemma rc15_mem_member_of_nonMem_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 : Finset (Finset α)}
  {a : α}
  {K : Finset α}
-- given
  (h𝒜 : rc15_UpperOn E 𝒜)
  (haE : a ∈ E)
  (hKE : K ⊆ E)
  (haK : a ∉ K)
  (hK : K ∈ 𝒜) :
-- imply
  K ∈ 𝒜.memberSubfamily a := by
-- proof
  apply StatMech.Walls.rc15_mem_member_of_nonMem h𝒜 a haE hKE haK hK

/--
[rc15_boxE_mem_erase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc15dimreduce.lean)
-/
@[path]
private lemma rc15_boxE_mem_erase_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {E : Finset α}
  {a : α}
  {S : Finset α}
-- given
  (h𝒜 : rc15_UpperOn E 𝒜)
  (haE : a ∈ E)
  (haS : a ∈ S)
  (hSE : S ⊆ E) :
-- imply
  S.erase a ∈ (rc14_boxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a) ∪ rc14_boxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a)) ↔ S ∈ rc14_boxE E 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc15_boxE_mem_erase h𝒜 a S haE haS hSE

/--
[rc15_boxE_mem_id](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc15dimreduce.lean)
-/
@[path]
private lemma rc15_boxE_mem_id_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {E : Finset α}
  {a : α}
  {S : Finset α}
-- given
  (haS : a ∉ S)
  (hSE : S ⊆ E) :
-- imply
  S ∈ rc14_boxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a) ↔ S ∈ rc14_boxE E 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc15_boxE_mem_id 𝒜 ℬ E a S haS hSE

/--
[rc15_card_boxE_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc15dimreduce.lean)
-/
@[path]
private lemma rc15_card_boxE_slice_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {E : Finset α}
  {a : α}
-- given
  (h𝒜 : rc15_UpperOn E 𝒜)
  (haE : a ∈ E) :
-- imply
  #(rc14_boxE E 𝒜 ℬ) = #(rc14_boxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a)) + #(rc14_boxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a) ∪ rc14_boxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a)) := by
-- proof
  apply StatMech.Walls.rc15_card_boxE_slice h𝒜 a haE

/--
[rc15_reflE_left_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc15dimreduce.lean)
-/
@[path]
private lemma rc15_reflE_left_subset_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 𝒜' ℬ : Finset (Finset α)}
-- given
  (h : 𝒜 ⊆ 𝒜') :
-- imply
  rc14_reflE E 𝒜 ℬ ⊆ rc14_reflE E 𝒜' ℬ := by
-- proof
  apply StatMech.Walls.rc15_reflE_left_subset h

/--
[rc15_reflE_nonMem_subset_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc15dimreduce.lean)
-/
@[path]
private lemma rc15_reflE_nonMem_subset_mem_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 ℬ : Finset (Finset α)}
  {a : α}
-- given
  (h𝒜 : rc15_UpperOn E 𝒜)
  (haE : a ∈ E) :
-- imply
  rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) ℬ ⊆ rc14_reflE (E.erase a) (𝒜.memberSubfamily a) ℬ := by
-- proof
  apply StatMech.Walls.rc15_reflE_nonMem_subset_mem h𝒜 a haE

/--
[rc15_card_reflE_nonMem_le_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc15dimreduce.lean)
-/
@[path]
private lemma rc15_card_reflE_nonMem_le_mem_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 ℬ : Finset (Finset α)}
  {a : α}
-- given
  (h𝒜 : rc15_UpperOn E 𝒜)
  (haE : a ∈ E) :
-- imply
  #(rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) ℬ) ≤ #(rc14_reflE (E.erase a) (𝒜.memberSubfamily a) ℬ) := by
-- proof
  apply StatMech.Walls.rc15_card_reflE_nonMem_le_mem h𝒜 a haE

/--
[rc15_bkrground_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc15dimreduce.lean)
-/
@[path]
private lemma rc15_bkrground_empty_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc15_BKRground (∅ : Finset α) := by
-- proof
  apply StatMech.Walls.rc15_bkrground_empty

/--
[rc15_bkrground_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc15dimreduce.lean)
-/
@[path]
private lemma rc15_bkrground_step_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {a : α}
-- given
  (hUnion : rc15_SliceUnionBound (α := α))
  (haE : a ∈ E)
  (hIH : rc15_BKRground (E.erase a)) :
-- imply
  rc15_BKRground E := by
-- proof
  apply StatMech.Walls.rc15_bkrground_step hUnion haE hIH

/--
[rc15_bkrground_of_sliceUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc15dimreduce.lean)
-/
@[path]
private lemma rc15_bkrground_of_sliceUnion_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (hUnion : rc15_SliceUnionBound (α := α)) :
-- imply
  ∀ E : Finset α, rc15_BKRground E := by
-- proof
  apply StatMech.Walls.rc15_bkrground_of_sliceUnion hUnion

/--
[rc15_boxE_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc15dimreduce.lean)
-/
@[path]
private lemma rc15_boxE_univ_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc14_boxE (univ : Finset α) 𝒜 ℬ = rc10_boxSupp 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc15_boxE_univ 𝒜 ℬ

/--
[rc15_reflE_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc15dimreduce.lean)
-/
@[path]
private lemma rc15_reflE_univ_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc14_reflE (univ : Finset α) 𝒜 ℬ = rc10_reflInter 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc15_reflE_univ 𝒜 ℬ

/--
[rc15_bkrSetFamily_of_bkrground](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc15dimreduce.lean)
-/
@[path]
private lemma rc15_bkrSetFamily_of_bkrground_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : ∀ (β : Type) [Fintype β] [DecidableEq β], rc15_BKRground (univ : Finset β)) :
-- imply
  rc10_BKRSetFamily := by
-- proof
  apply StatMech.Walls.rc15_bkrSetFamily_of_bkrground h

/--
[rc15_bkrSetFamily_of_sliceUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc15dimreduce.lean)
-/
@[path]
private lemma rc15_bkrSetFamily_of_sliceUnion_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (hUnion : ∀ (β : Type) [Fintype β] [DecidableEq β], rc15_SliceUnionBound (α := β)) :
-- imply
  rc10_BKRSetFamily := by
-- proof
  apply StatMech.Walls.rc15_bkrSetFamily_of_sliceUnion hUnion

/--
[rc15_sliceUnion_empty_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc15dimreduce.lean)
-/
@[path]
private lemma rc15_sliceUnion_empty_left_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {ℬ : Finset (Finset α)}
  {a : α} :
-- imply
  #(rc14_boxE (E.erase a) ((∅ : Finset (Finset α)).memberSubfamily a) (ℬ.nonMemberSubfamily a) ∪ rc14_boxE (E.erase a) ((∅ : Finset (Finset α)).nonMemberSubfamily a) (ℬ.memberSubfamily a)) ≤ #(rc14_reflE (E.erase a) ((∅ : Finset (Finset α)).nonMemberSubfamily a) (ℬ.memberSubfamily a)) := by
-- proof
  apply StatMech.Walls.rc15_sliceUnion_empty_left ℬ a


-- created on 2026-10-23
