import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc6eventdowncompression
open Finset StatMech StatMech.Walls


/--
[rc6_downComp_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6eventdowncompression.lean)
-/
@[path]
private lemma rc6_downComp_card_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  #(Down.compression i 𝒜) = #𝒜 := by
-- proof
  apply StatMech.Walls.rc6_downComp_card i 𝒜

/--
[rc6_downComp_idem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6eventdowncompression.lean)
-/
@[path]
private lemma rc6_downComp_idem_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  Down.compression i (Down.compression i 𝒜) = Down.compression i 𝒜 := by
-- proof
  apply StatMech.Walls.rc6_downComp_idem i 𝒜

/--
[rc6_downComp_eq_self_of_isLowerSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6eventdowncompression.lean)
-/
@[path]
private lemma rc6_downComp_eq_self_of_isLowerSet_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)}
  {i : α}
-- given
  (h : IsLowerSet (𝒜 : Set (Finset α))) :
-- imply
  Down.compression i 𝒜 = 𝒜 := by
-- proof
  apply StatMech.Walls.rc6_downComp_eq_self_of_isLowerSet h i

/--
[rc6_card_member_add_nonMember](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6eventdowncompression.lean)
-/
@[path]
private lemma rc6_card_member_add_nonMember_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  #(𝒜.memberSubfamily i) + #(𝒜.nonMemberSubfamily i) = #𝒜 := by
-- proof
  apply StatMech.Walls.rc6_card_member_add_nonMember i 𝒜

/--
[rc6_member_union_nonMember](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6eventdowncompression.lean)
-/
@[path]
private lemma rc6_member_union_nonMember_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  𝒜.memberSubfamily i ∪ 𝒜.nonMemberSubfamily i = 𝒜.image (fun s => s.erase i) := by
-- proof
  apply StatMech.Walls.rc6_member_union_nonMember i 𝒜

/--
[rc6_member_subset_nonMember_of_isLowerSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6eventdowncompression.lean)
-/
@[path]
private lemma rc6_member_subset_nonMember_of_isLowerSet_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)}
  {i : α}
-- given
  (h : IsLowerSet (𝒜 : Set (Finset α))) :
-- imply
  𝒜.memberSubfamily i ⊆ 𝒜.nonMemberSubfamily i := by
-- proof
  apply StatMech.Walls.rc6_member_subset_nonMember_of_isLowerSet h i

/--
[rc6_downComp_member_subset_nonMember](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6eventdowncompression.lean)
-/
@[path]
private lemma rc6_downComp_member_subset_nonMember_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  (Down.compression i 𝒜).memberSubfamily i ⊆ (Down.compression i 𝒜).nonMemberSubfamily i := by
-- proof
  apply StatMech.Walls.rc6_downComp_member_subset_nonMember i 𝒜

/--
[rc6_event_down_compression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6eventdowncompression.lean)
-/
@[path]
private lemma rc6_event_down_compression_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  #(Down.compression i 𝒜) = #𝒜 ∧ Down.compression i (Down.compression i 𝒜) = Down.compression i 𝒜 ∧ (IsLowerSet (𝒜 : Set (Finset α)) → Down.compression i 𝒜 = 𝒜) ∧ #(𝒜.memberSubfamily i) + #(𝒜.nonMemberSubfamily i) = #𝒜 ∧ 𝒜.memberSubfamily i ∪ 𝒜.nonMemberSubfamily i = 𝒜.image (fun s => s.erase i) ∧ (IsLowerSet (𝒜 : Set (Finset α)) → 𝒜.memberSubfamily i ⊆ 𝒜.nonMemberSubfamily i) ∧ (Down.compression i 𝒜).memberSubfamily i ⊆ (Down.compression i 𝒜).nonMemberSubfamily i := by
-- proof
  apply StatMech.Walls.rc6_event_down_compression i 𝒜

/--
[rc6_downComp_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6eventdowncompression.lean)
-/
@[path]
private lemma rc6_downComp_empty_eq
  [DecidableEq α]
  {i : α} :
-- imply
  Down.compression i (∅ : Finset (Finset α)) = ∅ := by
-- proof
  apply StatMech.Walls.rc6_downComp_empty i

/--
[rc6_downComp_singleton_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6eventdowncompression.lean)
-/
@[path]
private lemma rc6_downComp_singleton_empty_eq
  [DecidableEq α]
  {i : α} :
-- imply
  Down.compression i ({∅} : Finset (Finset α)) = {∅} := by
-- proof
  apply StatMech.Walls.rc6_downComp_singleton_empty i

/--
[rc6_downComp_card_powerset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6eventdowncompression.lean)
-/
@[path]
private lemma rc6_downComp_card_powerset_eq
  [DecidableEq α]
  {i : α}
  {s : Finset α} :
-- imply
  #(Down.compression i s.powerset) = 2 ^ s.card := by
-- proof
  apply StatMech.Walls.rc6_downComp_card_powerset i s


-- created on 2026-10-23
