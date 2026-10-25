import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc6blmonovariant
open Finset StatMech StatMech.Walls


/--
[rc6_totalSize_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6blmonovariant.lean)
-/
@[path]
private lemma rc6_totalSize_eq_sum_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)} :
-- imply
  totalSize 𝒜 = ∑ S ∈ 𝒜, S.card := by
-- proof
  apply StatMech.Walls.rc6_totalSize_eq_sum 𝒜

/--
[rc6_totalSize_nonincreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6blmonovariant.lean)
-/
@[path]
private lemma rc6_totalSize_nonincreasing_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  totalSize (Down.compression i 𝒜) ≤ totalSize 𝒜 := by
-- proof
  apply StatMech.Walls.rc6_totalSize_nonincreasing i 𝒜

/--
[rc6_totalSize_strictly_drops](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6blmonovariant.lean)
-/
@[path]
private lemma rc6_totalSize_strictly_drops_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)}
-- given
  (hne : Down.compression i 𝒜 ≠ 𝒜) :
-- imply
  totalSize (Down.compression i 𝒜) < totalSize 𝒜 := by
-- proof
  apply StatMech.Walls.rc6_totalSize_strictly_drops i 𝒜 hne

/--
[rc6_isLowerSet_iff_fixedByAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6blmonovariant.lean)
-/
@[path]
private lemma rc6_isLowerSet_iff_fixedByAll_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)} :
-- imply
  IsLowerSet (𝒜 : Set (Finset α)) ↔ ∀ i : α, Down.compression i 𝒜 = 𝒜 := by
-- proof
  apply StatMech.Walls.rc6_isLowerSet_iff_fixedByAll 𝒜

/--
[rc6_exists_nonfixpoint_of_not_isLowerSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6blmonovariant.lean)
-/
@[path]
private lemma rc6_exists_nonfixpoint_of_not_isLowerSet_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)}
-- given
  (h : ¬ IsLowerSet (𝒜 : Set (Finset α))) :
-- imply
  ∃ i : α, totalSize (Down.compression i 𝒜) < totalSize 𝒜 := by
-- proof
  apply StatMech.Walls.rc6_exists_nonfixpoint_of_not_isLowerSet h

/--
[rc6_sweep_reaches_downset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6blmonovariant.lean)
-/
@[path]
private lemma rc6_sweep_reaches_downset_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)} :
-- imply
  ∃ cs : List α, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset α)) ∧ (iterDownComp cs 𝒜).card = 𝒜.card := by
-- proof
  apply StatMech.Walls.rc6_sweep_reaches_downset 𝒜

/--
[rc6_blMonovariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6blmonovariant.lean)
-/
@[path]
private lemma rc6_blMonovariant_eq
  [DecidableEq α] :
-- imply
  (∀ (i : α) (𝒜 : Finset (Finset α)), Down.compression i 𝒜 ≠ 𝒜 → totalSize (Down.compression i 𝒜) < totalSize 𝒜) ∧ (∀ (i : α) (𝒜 : Finset (Finset α)), totalSize (Down.compression i 𝒜) ≤ totalSize 𝒜) ∧ (∀ 𝒜 : Finset (Finset α), IsLowerSet (𝒜 : Set (Finset α)) ↔ ∀ i : α, Down.compression i 𝒜 = 𝒜) ∧ (∀ 𝒜 : Finset (Finset α), ∃ cs : List α, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset α)) ∧ (iterDownComp cs 𝒜).card = 𝒜.card) := by
-- proof
  apply StatMech.Walls.rc6_blMonovariant

/--
[rc6_blMonovariant_assembly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6blmonovariant.lean)
-/
@[path]
private lemma rc6_blMonovariant_assembly_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)} :
-- imply
  (∀ (i : α) (ℬ : Finset (Finset α)), Down.compression i ℬ ≠ ℬ → totalSize (Down.compression i ℬ) < totalSize ℬ) ∧ (∀ ℬ : Finset (Finset α), IsLowerSet (ℬ : Set (Finset α)) ↔ ∀ i : α, Down.compression i ℬ = ℬ) ∧ (∃ cs : List α, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset α)) ∧ (iterDownComp cs 𝒜).card = 𝒜.card) := by
-- proof
  apply StatMech.Walls.rc6_blMonovariant_assembly 𝒜

/--
[rc6_sweep_isLowerSet_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6blmonovariant.lean)
-/
@[path]
private lemma rc6_sweep_isLowerSet_self_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)}
-- given
  (h : IsLowerSet (𝒜 : Set (Finset α))) :
-- imply
  IsLowerSet ((iterDownComp ([] : List α) 𝒜) : Set (Finset α)) ∧ (iterDownComp ([] : List α) 𝒜).card = 𝒜.card := by
-- proof
  apply StatMech.Walls.rc6_sweep_isLowerSet_self h

/--
[rc6_univ_isLowerSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6blmonovariant.lean)
-/
@[path]
private lemma rc6_univ_isLowerSet_eq
  [DecidableEq α]
  [Fintype α] :
-- imply
  IsLowerSet ((Finset.univ : Finset (Finset α)) : Set (Finset α)) := by
-- proof
  apply StatMech.Walls.rc6_univ_isLowerSet

/--
[rc6_strict_drop_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6blmonovariant.lean)
-/
@[path]
private lemma rc6_strict_drop_singleton_eq
  [DecidableEq α]
  {a : α} :
-- imply
  totalSize (Down.compression a ({{a}} : Finset (Finset α))) < totalSize ({{a}} : Finset (Finset α)) := by
-- proof
  apply StatMech.Walls.rc6_strict_drop_singleton a


-- created on 2026-10-23
