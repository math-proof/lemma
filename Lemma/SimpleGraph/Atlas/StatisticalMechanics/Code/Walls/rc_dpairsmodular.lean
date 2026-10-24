import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc_dpairsmodular
open Finset StatMech StatMech.Walls


/--
[rc_dkern_self_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_dpairsmodular.lean)
-/
@[path]
private lemma rc_dkern_self_disjoint_eq
  [DecidableEq α]
  {S T : Finset α}
-- given
  (h : Disjoint S T) :
-- imply
  rc_dkern S T = 1 := by
-- proof
  apply StatMech.Walls.rc_dkern_self_disjoint h

/--
[rc_dkern_not_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_dpairsmodular.lean)
-/
@[path]
private lemma rc_dkern_not_disjoint_eq
  [DecidableEq α]
  {S T : Finset α}
-- given
  (h : ¬ Disjoint S T) :
-- imply
  rc_dkern S T = 0 := by
-- proof
  apply StatMech.Walls.rc_dkern_not_disjoint h

/--
[rc_dkern_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_dpairsmodular.lean)
-/
@[path]
private lemma rc_dkern_comm_eq
  [DecidableEq α]
  {S T : Finset α} :
-- imply
  rc_dkern S T = rc_dkern T S := by
-- proof
  apply StatMech.Walls.rc_dkern_comm S T

/--
[rc_dpairsCount_eq_doubleSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_dpairsmodular.lean)
-/
@[path]
private lemma rc_dpairsCount_eq_doubleSum_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  dpairsCount 𝒜 ℬ = ∑ S ∈ 𝒜, ∑ T ∈ ℬ, rc_dkern S T := by
-- proof
  apply StatMech.Walls.rc_dpairsCount_eq_doubleSum 𝒜 ℬ

/--
[rc_dpairsCount_eq_sum_card_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_dpairsmodular.lean)
-/
@[path]
private lemma rc_dpairsCount_eq_sum_card_fst_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  dpairsCount 𝒜 ℬ = ∑ S ∈ 𝒜, (ℬ.filter (fun T => Disjoint S T)).card := by
-- proof
  apply StatMech.Walls.rc_dpairsCount_eq_sum_card_fst 𝒜 ℬ

/--
[rc_dpairsCount_eq_sum_card_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_dpairsmodular.lean)
-/
@[path]
private lemma rc_dpairsCount_eq_sum_card_snd_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  dpairsCount 𝒜 ℬ = ∑ T ∈ ℬ, (𝒜.filter (fun S => Disjoint S T)).card := by
-- proof
  apply StatMech.Walls.rc_dpairsCount_eq_sum_card_snd 𝒜 ℬ

/--
[rc_dpairsCount_mono_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_dpairsmodular.lean)
-/
@[path]
private lemma rc_dpairsCount_mono_fst_eq
  [DecidableEq α]
  {𝒜 𝒜' ℬ : Finset (Finset α)}
-- given
  (h : 𝒜 ⊆ 𝒜') :
-- imply
  dpairsCount 𝒜 ℬ ≤ dpairsCount 𝒜' ℬ := by
-- proof
  apply StatMech.Walls.rc_dpairsCount_mono_fst h

/--
[rc_dpairsCount_mono_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_dpairsmodular.lean)
-/
@[path]
private lemma rc_dpairsCount_mono_snd_eq
  [DecidableEq α]
  {𝒜 ℬ ℬ' : Finset (Finset α)}
-- given
  (h : ℬ ⊆ ℬ') :
-- imply
  dpairsCount 𝒜 ℬ ≤ dpairsCount 𝒜 ℬ' := by
-- proof
  apply StatMech.Walls.rc_dpairsCount_mono_snd h

/--
[rc_dpairsCount_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_dpairsmodular.lean)
-/
@[path]
private lemma rc_dpairsCount_mono_eq
  [DecidableEq α]
  {𝒜 𝒜' ℬ ℬ' : Finset (Finset α)}
-- given
  (hA : 𝒜 ⊆ 𝒜')
  (hB : ℬ ⊆ ℬ') :
-- imply
  dpairsCount 𝒜 ℬ ≤ dpairsCount 𝒜' ℬ' := by
-- proof
  apply StatMech.Walls.rc_dpairsCount_mono hA hB

/--
[rc_dpairsCount_union_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_dpairsmodular.lean)
-/
@[path]
private lemma rc_dpairsCount_union_fst_eq
  [DecidableEq α]
  {𝒜 𝒜' ℬ : Finset (Finset α)}
-- given
  (h : Disjoint 𝒜 𝒜') :
-- imply
  dpairsCount (𝒜 ∪ 𝒜') ℬ = dpairsCount 𝒜 ℬ + dpairsCount 𝒜' ℬ := by
-- proof
  apply StatMech.Walls.rc_dpairsCount_union_fst h

/--
[rc_dpairsCount_union_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_dpairsmodular.lean)
-/
@[path]
private lemma rc_dpairsCount_union_snd_eq
  [DecidableEq α]
  {𝒜 ℬ ℬ' : Finset (Finset α)}
-- given
  (h : Disjoint ℬ ℬ') :
-- imply
  dpairsCount 𝒜 (ℬ ∪ ℬ') = dpairsCount 𝒜 ℬ + dpairsCount 𝒜 ℬ' := by
-- proof
  apply StatMech.Walls.rc_dpairsCount_union_snd h

/--
[rc_dpairsCount_modular_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_dpairsmodular.lean)
-/
@[path]
private lemma rc_dpairsCount_modular_fst_eq
  [DecidableEq α]
  {𝒜 𝒜' ℬ : Finset (Finset α)} :
-- imply
  dpairsCount (𝒜 ∪ 𝒜') ℬ + dpairsCount (𝒜 ∩ 𝒜') ℬ = dpairsCount 𝒜 ℬ + dpairsCount 𝒜' ℬ := by
-- proof
  apply StatMech.Walls.rc_dpairsCount_modular_fst 𝒜 𝒜' ℬ

/--
[rc_dpairsCount_modular_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_dpairsmodular.lean)
-/
@[path]
private lemma rc_dpairsCount_modular_snd_eq
  [DecidableEq α]
  {𝒜 ℬ ℬ' : Finset (Finset α)} :
-- imply
  dpairsCount 𝒜 (ℬ ∪ ℬ') + dpairsCount 𝒜 (ℬ ∩ ℬ') = dpairsCount 𝒜 ℬ + dpairsCount 𝒜 ℬ' := by
-- proof
  apply StatMech.Walls.rc_dpairsCount_modular_snd 𝒜 ℬ ℬ'

/--
[rc_dpairsCount_empty_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_dpairsmodular.lean)
-/
@[path]
private lemma rc_dpairsCount_empty_fst_eq
  [DecidableEq α]
  {ℬ : Finset (Finset α)} :
-- imply
  dpairsCount (∅ : Finset (Finset α)) ℬ = 0 := by
-- proof
  apply StatMech.Walls.rc_dpairsCount_empty_fst ℬ

/--
[rc_dpairsCount_empty_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_dpairsmodular.lean)
-/
@[path]
private lemma rc_dpairsCount_empty_snd_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)} :
-- imply
  dpairsCount 𝒜 (∅ : Finset (Finset α)) = 0 := by
-- proof
  apply StatMech.Walls.rc_dpairsCount_empty_snd 𝒜

/--
[rc_dpairsCount_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_dpairsmodular.lean)
-/
@[path]
private lemma rc_dpairsCount_comm_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  dpairsCount 𝒜 ℬ = dpairsCount ℬ 𝒜 := by
-- proof
  apply StatMech.Walls.rc_dpairsCount_comm 𝒜 ℬ


-- created on 2026-10-23
