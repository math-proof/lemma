import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc2_blendpoint
open Finset StatMech StatMech.Walls


/--
[rc2_blendpoint_converges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_blendpoint.lean)
-/
@[path]
private lemma rc2_blendpoint_converges_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)} :
-- imply
  ∃ cs : List α, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset α)) ∧ (∀ ℬ : Finset (Finset α), dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ)) ∧ (iterDownComp cs 𝒜).card = 𝒜.card := by
-- proof
  apply StatMech.Walls.rc2_blendpoint_converges 𝒜

/--
[rc2_blendpoint_favourable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_blendpoint.lean)
-/
@[path]
private lemma rc2_blendpoint_favourable_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α}
-- given
  (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
  (hℬ : IsLowerSet (ℬ : Set (Finset α))) :
-- imply
  dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i) := by
-- proof
  apply StatMech.Walls.rc2_blendpoint_favourable h𝒜 hℬ i

/--
[rc2_blendpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_blendpoint.lean)
-/
@[path]
private lemma rc2_blendpoint_eq
  [DecidableEq α] :
-- imply
  (∀ 𝒜 : Finset (Finset α), ∃ cs : List α, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset α)) ∧ ∀ ℬ : Finset (Finset α), dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ)) ∧ (∀ {𝒜 ℬ : Finset (Finset α)}, IsLowerSet (𝒜 : Set (Finset α)) → IsLowerSet (ℬ : Set (Finset α)) → ∀ i : α, dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)) := by
-- proof
  apply StatMech.Walls.rc2_blendpoint

/--
[rc2_iterDownComp_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_blendpoint.lean)
-/
@[path]
private lemma rc2_iterDownComp_append_eq
  [DecidableEq α]
  {cs₁ cs₂ : List α}
  {𝒜 : Finset (Finset α)} :
-- imply
  iterDownComp (cs₁ ++ cs₂) 𝒜 = iterDownComp cs₁ (iterDownComp cs₂ 𝒜) := by
-- proof
  apply StatMech.Walls.rc2_iterDownComp_append cs₁ cs₂ 𝒜

/--
[rc2_blendpoint_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_blendpoint.lean)
-/
@[path]
private lemma rc2_blendpoint_pair_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  ∃ cs : List α, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset α)) ∧ IsLowerSet ((iterDownComp cs ℬ) : Set (Finset α)) ∧ dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ) ∧ (iterDownComp cs 𝒜).card = 𝒜.card ∧ (iterDownComp cs ℬ).card = ℬ.card := by
-- proof
  apply StatMech.Walls.rc2_blendpoint_pair 𝒜 ℬ

/--
[rc2_blendpoint_deficit_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_blendpoint.lean)
-/
@[path]
private lemma rc2_blendpoint_deficit_nonneg_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α}
-- given
  (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
  (hℬ : IsLowerSet (ℬ : Set (Finset α))) :
-- imply
  (0 : ℤ) ≤ (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ) - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i) ∧ dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i) := by
-- proof
  apply StatMech.Walls.rc2_blendpoint_deficit_nonneg h𝒜 hℬ i

/--
[rc2_blendpoint_favourable_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_blendpoint.lean)
-/
@[path]
private lemma rc2_blendpoint_favourable_self_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)}
  {i : α}
-- given
  (h𝒜 : IsLowerSet (𝒜 : Set (Finset α))) :
-- imply
  dpairsCount (𝒜.memberSubfamily i) (𝒜.memberSubfamily i) ≤ dpairsCount (𝒜.nonMemberSubfamily i) (𝒜.nonMemberSubfamily i) := by
-- proof
  apply StatMech.Walls.rc2_blendpoint_favourable_self h𝒜 i

/--
[rc2_blendpoint_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_blendpoint.lean)
-/
@[path]
private lemma rc2_blendpoint_empty_eq
  [DecidableEq α] :
-- imply
  IsLowerSet ((iterDownComp ([] : List α) (∅ : Finset (Finset α))) : Set (Finset α)) ∧ (iterDownComp ([] : List α) (∅ : Finset (Finset α))).card = 0 := by
-- proof
  apply StatMech.Walls.rc2_blendpoint_empty

/--
[rc2_blendpoint_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_blendpoint.lean)
-/
@[path]
private lemma rc2_blendpoint_univ_eq
  [DecidableEq α]
  [Fintype α] :
-- imply
  IsLowerSet ((iterDownComp ([] : List α) (Finset.univ : Finset (Finset α))) : Set (Finset α)) := by
-- proof
  apply StatMech.Walls.rc2_blendpoint_univ


-- created on 2026-10-23
