import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc16menger.Part4
open StatMech StatMech.Walls


/--
[bc16_univ_isSeparator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc16menger.lean)
-/
@[path]
private lemma bc16_univ_isSeparator_eq
  {V : Type u}
  {G : SimpleGraph V}
  {G : SimpleGraph V}
  {S T : Set V} :
-- imply
  bc16_IsSeparator G S T Set.univ := by
-- proof
  apply StatMech.Walls.bc16_univ_isSeparator G S T

/--
[bc16_separator_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc16menger.lean)
-/
@[path]
private lemma bc16_separator_mono_eq
  {V : Type u}
  {G : SimpleGraph V}
  {S T C C' : Set V}
-- given
  (h : bc16_IsSeparator G S T C)
  (hCC' : C ⊆ C') :
-- imply
  bc16_IsSeparator G S T C' := by
-- proof
  apply StatMech.Walls.bc16_separator_mono h hCC'

/--
[bc16_separator_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc16menger.lean)
-/
@[path]
private lemma bc16_separator_symm_eq
  {V : Type u}
  {G : SimpleGraph V}
  {S T C : Set V}
-- given
  (h : bc16_IsSeparator G S T C) :
-- imply
  bc16_IsSeparator G T S C := by
-- proof
  apply StatMech.Walls.bc16_separator_symm h

/--
[bc16_separator_hits_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc16menger.lean)
-/
@[path]
private lemma bc16_separator_hits_path_eq
  {V : Type u}
  {G : SimpleGraph V}
  {S T C : Set V}
  {F : bc16_DisjointPathFamily G S T ι}
  {i : ι}
-- given
  (hC : bc16_IsSeparator G S T C) :
-- imply
  ∃ c ∈ C, c ∈ (F.p i).support := by
-- proof
  apply StatMech.Walls.bc16_separator_hits_path F hC i

/--
[bc16_hitVertex_mem_separator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc16menger.lean)
-/
@[path]
private lemma bc16_hitVertex_mem_separator_eq
  {V : Type u}
  {G : SimpleGraph V}
  {S T C : Set V}
  {F : bc16_DisjointPathFamily G S T ι}
  {i : ι}
-- given
  (hC : bc16_IsSeparator G S T C) :
-- imply
  bc16_hitVertex F hC i ∈ C := by
-- proof
  apply StatMech.Walls.bc16_hitVertex_mem_separator F hC i

/--
[bc16_hitVertex_mem_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc16menger.lean)
-/
@[path]
private lemma bc16_hitVertex_mem_support_eq
  {V : Type u}
  {G : SimpleGraph V}
  {S T C : Set V}
  {F : bc16_DisjointPathFamily G S T ι}
  {i : ι}
-- given
  (hC : bc16_IsSeparator G S T C) :
-- imply
  bc16_hitVertex F hC i ∈ (F.p i).support := by
-- proof
  apply StatMech.Walls.bc16_hitVertex_mem_support F hC i

/--
[bc16_hitVertex_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc16menger.lean)
-/
@[path]
private lemma bc16_hitVertex_injective_eq
  {V : Type u}
  {G : SimpleGraph V}
  {S T C : Set V}
  {F : bc16_DisjointPathFamily G S T ι}
-- given
  (hC : bc16_IsSeparator G S T C) :
-- imply
  Function.Injective (bc16_hitVertex F hC) := by
-- proof
  apply StatMech.Walls.bc16_hitVertex_injective F hC

/--
[bc16_max_le_min](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc16menger.lean)
-/
@[path]
private lemma bc16_max_le_min_eq
  {V : Type u}
  {G : SimpleGraph V}
  {S T C : Set V}
  {F : bc16_DisjointPathFamily G S T ι}
-- given
  (hC : bc16_IsSeparator G S T C)
  (hCfin : C.Finite) :
-- imply
  (Set.univ : Set ι).ncard ≤ C.ncard := by
-- proof
  apply StatMech.Walls.bc16_max_le_min F hC hCfin

/--
[bc16_card_le_ncard_separator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc16menger.lean)
-/
@[path]
private lemma bc16_card_le_ncard_separator_eq
  {V : Type u}
  {G : SimpleGraph V}
  {S T C : Set V}
  [Finite V]
  [Fintype ι]
  {F : bc16_DisjointPathFamily G S T ι}
-- given
  (hC : bc16_IsSeparator G S T C) :
-- imply
  Fintype.card ι ≤ C.ncard := by
-- proof
  apply StatMech.Walls.bc16_card_le_ncard_separator F hC

/--
[bc16_encard_le_encard_separator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc16menger.lean)
-/
@[path]
private lemma bc16_encard_le_encard_separator_eq
  {V : Type u}
  {G : SimpleGraph V}
  {S T C : Set V}
  {F : bc16_DisjointPathFamily G S T ι}
-- given
  (hC : bc16_IsSeparator G S T C) :
-- imply
  (Set.univ : Set ι).encard ≤ C.encard := by
-- proof
  apply StatMech.Walls.bc16_encard_le_encard_separator F hC

/--
[bc16_source_isSeparator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc16menger.lean)
-/
@[path]
private lemma bc16_source_isSeparator_eq
  {V : Type u}
  {G : SimpleGraph V}
  {G : SimpleGraph V}
  {S T : Set V} :
-- imply
  bc16_IsSeparator G S T S := by
-- proof
  apply StatMech.Walls.bc16_source_isSeparator G S T

/--
[bc16_target_isSeparator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc16menger.lean)
-/
@[path]
private lemma bc16_target_isSeparator_eq
  {V : Type u}
  {G : SimpleGraph V}
  {G : SimpleGraph V}
  {S T : Set V} :
-- imply
  bc16_IsSeparator G S T T := by
-- proof
  apply StatMech.Walls.bc16_target_isSeparator G S T

/--
[bc16_no_walk_of_empty_separator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc16menger.lean)
-/
@[path]
private lemma bc16_no_walk_of_empty_separator_eq
  {V : Type u}
  {G : SimpleGraph V}
  {S T : Set V}
  {s t : V}
  {p : G.Walk s t}
-- given
  (h : bc16_IsSeparator G S T (∅ : Set V))
  (hs : s ∈ S)
  (ht : t ∈ T) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.bc16_no_walk_of_empty_separator h hs ht p

/--
[bc16_empty_separator_of_no_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc16menger.lean)
-/
@[path]
private lemma bc16_empty_separator_of_no_walk_eq
  {V : Type u}
  {G : SimpleGraph V}
  {S T : Set V}
-- given
  (h : ∀ ⦃s⦄, s ∈ S → ∀ ⦃t⦄, t ∈ T → IsEmpty (G.Walk s t)) :
-- imply
  bc16_IsSeparator G S T (∅ : Set V) := by
-- proof
  apply StatMech.Walls.bc16_empty_separator_of_no_walk h

/--
[bc16_empty_separator_iff_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc16menger.lean)
-/
@[path]
private lemma bc16_empty_separator_iff_not_reachable_eq
  {V : Type u}
  {G : SimpleGraph V}
  {S T : Set V} :
-- imply
  bc16_IsSeparator G S T (∅ : Set V) ↔ ∀ ⦃s⦄, s ∈ S → ∀ ⦃t⦄, t ∈ T → ¬ G.Reachable s t := by
-- proof
  apply StatMech.Walls.bc16_empty_separator_iff_not_reachable

/--
[bc16_exists_path_of_not_empty_separator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc16menger.lean)
-/
@[path]
private lemma bc16_exists_path_of_not_empty_separator_eq
  {V : Type u}
  {G : SimpleGraph V}
  {S T : Set V}
-- given
  (h : ¬ bc16_IsSeparator G S T (∅ : Set V)) :
-- imply
  ∃ (s : V) (_ : s ∈ S) (t : V) (_ : t ∈ T) (p : G.Walk s t), p.IsPath := by
-- proof
  apply StatMech.Walls.bc16_exists_path_of_not_empty_separator h

/--
[bc16_one_le_ncard_separator_of_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc16menger.lean)
-/
@[path]
private lemma bc16_one_le_ncard_separator_of_path_eq
  {V : Type u}
  {G : SimpleGraph V}
  {S T C : Set V}
  {s t : V}
  {p : G.Walk s t}
-- given
  (hs : s ∈ S)
  (ht : t ∈ T)
  (hp : p.IsPath)
  (hC : bc16_IsSeparator G S T C)
  (hCfin : C.Finite) :
-- imply
  1 ≤ C.ncard := by
-- proof
  apply StatMech.Walls.bc16_one_le_ncard_separator_of_path hs ht hp hC hCfin

/--
[bc16_encard_le_source_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc16menger.lean)
-/
@[path]
private lemma bc16_encard_le_source_target_eq
  {V : Type u}
  {G : SimpleGraph V}
  {S T : Set V}
  {F : bc16_DisjointPathFamily G S T ι} :
-- imply
  (Set.univ : Set ι).encard ≤ S.encard ∧ (Set.univ : Set ι).encard ≤ T.encard := by
-- proof
  apply StatMech.Walls.bc16_encard_le_source_target F


-- created on 2026-10-23
