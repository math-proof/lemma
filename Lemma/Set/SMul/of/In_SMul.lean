import Mathlib
import sympy.Basic
open Pointwise


namespace Cosets

/--
[coset_eq_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Cosets.lean)
-/
@[path]
lemma coset_eq_of_mem
  [Group G]
  {H : Subgroup G}
  {a b : G}
-- given
  (hb : b ∈ a • (H : Set G)) :
-- imply
  a • (H : Set G) = b • (H : Set G) := by
-- proof
  rw [leftCoset_eq_iff]
  exact (mem_leftCoset_iff a).mp hb

end Cosets

namespace Cosets

/--
[mem_leftCoset_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Cosets.lean)
-/
@[path]
lemma mem_leftCoset_self
  [Group G]
  {H : Subgroup G}
  {g : G} :
-- imply
  g ∈ g • (H : Set G) :=
-- proof
  mem_own_leftCoset H.toSubmonoid g

end Cosets

namespace Cosets

/--
[leftCosets_eq_or_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Cosets.lean)
-/
@[path]
lemma leftCosets_eq_or_disjoint
  [Group G]
  {H : Subgroup G}
  {a b : G} :
-- imply
  a • (H : Set G) = b • (H : Set G) ∨ Disjoint (a • (H : Set G)) (b • (H : Set G)) := by
-- proof
  by_cases h : a⁻¹ * b ∈ H
  · left
    exact (leftCoset_eq_iff H).mpr h
  · right
    rw [Set.disjoint_left]
    intro x hxa hxb
    apply h
    have ha : a⁻¹ * x ∈ (H : Set G) := (mem_leftCoset_iff a).mp hxa
    have hb : b⁻¹ * x ∈ (H : Set G) := (mem_leftCoset_iff b).mp hxb
    have key : a⁻¹ * b = (a⁻¹ * x) * (b⁻¹ * x)⁻¹ := by group
    rw [key]
    exact H.mul_mem ha (H.inv_mem hb)

end Cosets

namespace Cosets

/--
[leftCosets_partition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Cosets.lean)
-/
@[path]
lemma leftCosets_partition
  [Group G]
  {H : Subgroup G} :
-- imply
  (∀ g : G, ∃ a : G, g ∈ a • (H : Set G)) ∧ (∀ a b : G, a • (H : Set G) = b • (H : Set G) ∨ Disjoint (a • (H : Set G)) (b • (H : Set G))) :=
-- proof
  ⟨fun g => ⟨g, mem_leftCoset_self H g⟩, leftCosets_eq_or_disjoint H⟩

end Cosets


-- created on 2026-10-23
