import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc5_dpairsmodular
open Finset StatMech StatMech.Walls


/--
[rc5_dkern_self_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_dpairsmodular.lean)
-/
@[path]
private lemma rc5_dkern_self_disjoint_eq
  [DecidableEq α]
  {S T : Finset α}
-- given
  (h : Disjoint S T) :
-- imply
  rc5_dkern S T = 1 := by
-- proof
  apply StatMech.Walls.rc5_dkern_self_disjoint h

/--
[rc5_dkern_not_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_dpairsmodular.lean)
-/
@[path]
private lemma rc5_dkern_not_disjoint_eq
  [DecidableEq α]
  {S T : Finset α}
-- given
  (h : ¬ Disjoint S T) :
-- imply
  rc5_dkern S T = 0 := by
-- proof
  apply StatMech.Walls.rc5_dkern_not_disjoint h

/--
[rc5_dkern_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_dpairsmodular.lean)
-/
@[path]
private lemma rc5_dkern_comm_eq
  [DecidableEq α]
  {S T : Finset α} :
-- imply
  rc5_dkern S T = rc5_dkern T S := by
-- proof
  apply StatMech.Walls.rc5_dkern_comm S T

/--
[rc5_dpairsCount_eq_doubleSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_dpairsmodular.lean)
-/
@[path]
private lemma rc5_dpairsCount_eq_doubleSum_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  dpairsCount 𝒜 ℬ = ∑ S ∈ 𝒜, ∑ T ∈ ℬ, rc5_dkern S T := by
-- proof
  apply StatMech.Walls.rc5_dpairsCount_eq_doubleSum 𝒜 ℬ

/--
[rc5_dpairsCount_eq_sum_card_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_dpairsmodular.lean)
-/
@[path]
private lemma rc5_dpairsCount_eq_sum_card_fst_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  dpairsCount 𝒜 ℬ = ∑ S ∈ 𝒜, (ℬ.filter (fun T => Disjoint S T)).card := by
-- proof
  apply StatMech.Walls.rc5_dpairsCount_eq_sum_card_fst 𝒜 ℬ

/--
[rc5_dpairsCount_eq_sum_card_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_dpairsmodular.lean)
-/
@[path]
private lemma rc5_dpairsCount_eq_sum_card_snd_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  dpairsCount 𝒜 ℬ = ∑ T ∈ ℬ, (𝒜.filter (fun S => Disjoint S T)).card := by
-- proof
  apply StatMech.Walls.rc5_dpairsCount_eq_sum_card_snd 𝒜 ℬ

/--
[rc5_dpairsCount_mono_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_dpairsmodular.lean)
-/
@[path]
private lemma rc5_dpairsCount_mono_fst_eq
  [DecidableEq α]
  {𝒜 𝒜' ℬ : Finset (Finset α)}
-- given
  (h : 𝒜 ⊆ 𝒜') :
-- imply
  dpairsCount 𝒜 ℬ ≤ dpairsCount 𝒜' ℬ := by
-- proof
  apply StatMech.Walls.rc5_dpairsCount_mono_fst h

/--
[rc5_dpairsCount_mono_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_dpairsmodular.lean)
-/
@[path]
private lemma rc5_dpairsCount_mono_snd_eq
  [DecidableEq α]
  {𝒜 ℬ ℬ' : Finset (Finset α)}
-- given
  (h : ℬ ⊆ ℬ') :
-- imply
  dpairsCount 𝒜 ℬ ≤ dpairsCount 𝒜 ℬ' := by
-- proof
  apply StatMech.Walls.rc5_dpairsCount_mono_snd h

/--
[rc5_dpairsCount_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_dpairsmodular.lean)
-/
@[path]
private lemma rc5_dpairsCount_mono_eq
  [DecidableEq α]
  {𝒜 𝒜' ℬ ℬ' : Finset (Finset α)}
-- given
  (hA : 𝒜 ⊆ 𝒜')
  (hB : ℬ ⊆ ℬ') :
-- imply
  dpairsCount 𝒜 ℬ ≤ dpairsCount 𝒜' ℬ' := by
-- proof
  apply StatMech.Walls.rc5_dpairsCount_mono hA hB

/--
[rc5_dpairsCount_union_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_dpairsmodular.lean)
-/
@[path]
private lemma rc5_dpairsCount_union_fst_eq
  [DecidableEq α]
  {𝒜 𝒜' ℬ : Finset (Finset α)}
-- given
  (h : Disjoint 𝒜 𝒜') :
-- imply
  dpairsCount (𝒜 ∪ 𝒜') ℬ = dpairsCount 𝒜 ℬ + dpairsCount 𝒜' ℬ := by
-- proof
  apply StatMech.Walls.rc5_dpairsCount_union_fst h

/--
[rc5_dpairsCount_union_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_dpairsmodular.lean)
-/
@[path]
private lemma rc5_dpairsCount_union_snd_eq
  [DecidableEq α]
  {𝒜 ℬ ℬ' : Finset (Finset α)}
-- given
  (h : Disjoint ℬ ℬ') :
-- imply
  dpairsCount 𝒜 (ℬ ∪ ℬ') = dpairsCount 𝒜 ℬ + dpairsCount 𝒜 ℬ' := by
-- proof
  apply StatMech.Walls.rc5_dpairsCount_union_snd h

/--
[rc5_dpairsCount_modular_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_dpairsmodular.lean)
-/
@[path]
private lemma rc5_dpairsCount_modular_fst_eq
  [DecidableEq α]
  {𝒜 𝒜' ℬ : Finset (Finset α)} :
-- imply
  dpairsCount (𝒜 ∪ 𝒜') ℬ + dpairsCount (𝒜 ∩ 𝒜') ℬ = dpairsCount 𝒜 ℬ + dpairsCount 𝒜' ℬ := by
-- proof
  apply StatMech.Walls.rc5_dpairsCount_modular_fst 𝒜 𝒜' ℬ

/--
[rc5_dpairsCount_modular_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_dpairsmodular.lean)
-/
@[path]
private lemma rc5_dpairsCount_modular_snd_eq
  [DecidableEq α]
  {𝒜 ℬ ℬ' : Finset (Finset α)} :
-- imply
  dpairsCount 𝒜 (ℬ ∪ ℬ') + dpairsCount 𝒜 (ℬ ∩ ℬ') = dpairsCount 𝒜 ℬ + dpairsCount 𝒜 ℬ' := by
-- proof
  apply StatMech.Walls.rc5_dpairsCount_modular_snd 𝒜 ℬ ℬ'

/--
[rc5_dpairsCount_empty_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_dpairsmodular.lean)
-/
@[path]
private lemma rc5_dpairsCount_empty_fst_eq
  [DecidableEq α]
  {ℬ : Finset (Finset α)} :
-- imply
  dpairsCount (∅ : Finset (Finset α)) ℬ = 0 := by
-- proof
  apply StatMech.Walls.rc5_dpairsCount_empty_fst ℬ

/--
[rc5_dpairsCount_empty_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_dpairsmodular.lean)
-/
@[path]
private lemma rc5_dpairsCount_empty_snd_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)} :
-- imply
  dpairsCount 𝒜 (∅ : Finset (Finset α)) = 0 := by
-- proof
  apply StatMech.Walls.rc5_dpairsCount_empty_snd 𝒜

/--
[rc5_dpairsCount_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_dpairsmodular.lean)
-/
@[path]
private lemma rc5_dpairsCount_comm_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  dpairsCount 𝒜 ℬ = dpairsCount ℬ 𝒜 := by
-- proof
  apply StatMech.Walls.rc5_dpairsCount_comm 𝒜 ℬ

/--
[rc5_downComp_nonMemberSubfamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_dpairsmodular.lean)
-/
@[path]
private lemma rc5_downComp_nonMemberSubfamily_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  (Down.compression i 𝒜).nonMemberSubfamily i = 𝒜.memberSubfamily i ∪ 𝒜.nonMemberSubfamily i := by
-- proof
  apply StatMech.Walls.rc5_downComp_nonMemberSubfamily i 𝒜

/--
[rc5_downComp_memberSubfamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_dpairsmodular.lean)
-/
@[path]
private lemma rc5_downComp_memberSubfamily_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  (Down.compression i 𝒜).memberSubfamily i = 𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i := by
-- proof
  apply StatMech.Walls.rc5_downComp_memberSubfamily i 𝒜

/--
[rc5_fiber_downDown_ineq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_dpairsmodular.lean)
-/
@[path]
private lemma rc5_fiber_downDown_ineq_eq
  [DecidableEq α]
  {am an bm bn : Finset (Finset α)} :
-- imply
  dpairsCount an bn + dpairsCount am bn + dpairsCount an bm ≤ dpairsCount (am ∪ an) (bm ∪ bn) + dpairsCount (am ∩ an) (bm ∪ bn) + dpairsCount (am ∪ an) (bm ∩ bn) := by
-- proof
  apply StatMech.Walls.rc5_fiber_downDown_ineq am an bm bn

/--
[rc5_dpairsCount_downDown_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_dpairsmodular.lean)
-/
@[path]
private lemma rc5_dpairsCount_downDown_mono_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) := by
-- proof
  apply StatMech.Walls.rc5_dpairsCount_downDown_mono 𝒜 ℬ i

/--
[rc5_deficit_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_dpairsmodular.lean)
-/
@[path]
private lemma rc5_deficit_identity_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  (dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) : ℤ) - dpairsCount 𝒜 ℬ = (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ) - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i) := by
-- proof
  apply StatMech.Walls.rc5_deficit_identity 𝒜 ℬ i

/--
[rc5_deficit_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_dpairsmodular.lean)
-/
@[path]
private lemma rc5_deficit_nonneg_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  (0 : ℤ) ≤ (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ) - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i) := by
-- proof
  apply StatMech.Walls.rc5_deficit_nonneg 𝒜 ℬ i

/--
[rc5_card_boxDoubled_downDown_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_dpairsmodular.lean)
-/
@[path]
private lemma rc5_card_boxDoubled_downDown_mono_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  (boxDoubled 𝒜 ℬ).card ≤ (boxDoubled (Down.compression i 𝒜) (Down.compression i ℬ)).card := by
-- proof
  apply StatMech.Walls.rc5_card_boxDoubled_downDown_mono 𝒜 ℬ i

/--
[rc5_dpairsmodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_dpairsmodular.lean)
-/
@[path]
private lemma rc5_dpairsmodular_eq
  [DecidableEq α]
  {𝒜 𝒜' ℬ ℬ' : Finset (Finset α)}
  {i : α} :
-- imply
  (dpairsCount 𝒜 ℬ = ∑ S ∈ 𝒜, ∑ T ∈ ℬ, rc5_dkern S T) ∧ (𝒜 ⊆ 𝒜' → ℬ ⊆ ℬ' → dpairsCount 𝒜 ℬ ≤ dpairsCount 𝒜' ℬ') ∧ (dpairsCount (𝒜 ∪ 𝒜') ℬ + dpairsCount (𝒜 ∩ 𝒜') ℬ = dpairsCount 𝒜 ℬ + dpairsCount 𝒜' ℬ) ∧ (dpairsCount 𝒜 (ℬ ∪ ℬ') + dpairsCount 𝒜 (ℬ ∩ ℬ') = dpairsCount 𝒜 ℬ + dpairsCount 𝒜 ℬ') ∧ (dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ)) := by
-- proof
  apply StatMech.Walls.rc5_dpairsmodular 𝒜 𝒜' ℬ ℬ' i


-- created on 2026-10-23
