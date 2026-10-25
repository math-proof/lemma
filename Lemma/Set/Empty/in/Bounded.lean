import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.Building.BornologyGroups.Part3
open Set Filter Classical BornologicalGroupData BNPairBornology


namespace BornologicalGroupData

/--
[empty_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/BornologyGroups.lean)
-/
@[path]
lemma empty_mem
  [Group G]
  {bd : BornologicalGroupData G} :
-- imply
  ∅ ∈ bd.bounded :=
-- proof
  bd.subset_mem {1} (bd.singleton_mem 1) ∅ (empty_subset _)

end BornologicalGroupData

namespace BNPairBornology

/--
[isBounded_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/BornologyGroups.lean)
-/
@[path]
lemma isBounded_iff
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {E : Set G}
-- given
  (hcover : ∀ g : G, ∃ w : M.Group, g ∈ bp.bruhatCell w) :
-- imply
  @Bornology.IsBounded G (toBornology bp hcover) E ↔ IsBounded bp E :=
-- proof
  Bornology.isBounded_ofBounded_iff _

end BNPairBornology

/--
[bruhatCell_isBounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/BornologyGroups.lean)
-/
@[path]
private lemma bruhatCell_isBounded_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {w : M.Group} :
-- imply
  IsBounded bp (bp.bruhatCell w) := by
-- proof
  apply BNPairBornology.bruhatCell_isBounded bp w

/--
[isBounded_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/BornologyGroups.lean)
-/
@[path]
private lemma isBounded_subset_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {E F : Set G}
-- given
  (hE : IsBounded bp E)
  (hFE : F ⊆ E) :
-- imply
  IsBounded bp F := by
-- proof
  apply BNPairBornology.isBounded_subset bp hE hFE

/--
[isBounded_union](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/BornologyGroups.lean)
-/
@[path]
private lemma isBounded_union_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {E F : Set G}
-- given
  (hE : IsBounded bp E)
  (hF : IsBounded bp F) :
-- imply
  IsBounded bp (E ∪ F) := by
-- proof
  apply BNPairBornology.isBounded_union bp hE hF

/--
[singleton_isBounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/BornologyGroups.lean)
-/
@[path]
private lemma singleton_isBounded_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {g : G}
-- given
  (hcover : ∀ g : G, ∃ w : M.Group, g ∈ bp.bruhatCell w) :
-- imply
  IsBounded bp {g} := by
-- proof
  apply BNPairBornology.singleton_isBounded bp hcover g

/--
[empty_isBounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/BornologyGroups.lean)
-/
@[path]
private lemma empty_isBounded_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M} :
-- imply
  IsBounded bp ∅ := by
-- proof
  apply BNPairBornology.empty_isBounded bp


-- created on 2026-10-23
