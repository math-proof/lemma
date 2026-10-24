import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc71disjpreserving
open Finset StatMech StatMech.Walls


/--
[rc71_resolveMember_not_both](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc71disjpreserving.lean)
-/
@[path]
private lemma rc71_resolveMember_not_both_eq
  {n : ℕ}
  {i : Fin n}
  {U : Finset (Fin n ⊕ Fin n)} :
-- imply
  ¬ (Sum.inl i ∈ rc71_resolveMember i U ∧ Sum.inr i ∈ rc71_resolveMember i U) := by
-- proof
  apply StatMech.Walls.rc71_resolveMember_not_both i U

/--
[rc71_resolveLeft_disjPreserving_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc71disjpreserving.lean)
-/
@[path]
private lemma rc71_resolveLeft_disjPreserving_at_eq
  {n : ℕ}
  {i : Fin n}
  {Fam : Finset (Finset (Fin n ⊕ Fin n))} :
-- imply
  ∀ V ∈ rc71_resolveLeft i Fam, ¬ (Sum.inl i ∈ V ∧ Sum.inr i ∈ V) := by
-- proof
  apply StatMech.Walls.rc71_resolveLeft_disjPreserving_at i Fam

/--
[rc71_witness_disjPreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc71disjpreserving.lean)
-/
@[path]
private lemma rc71_witness_disjPreserving_eq
  {n : ℕ} :
-- imply
  rc70_DisjPreserving 2 (rc71_disjPreservingCompress 0 (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅})) := by
-- proof
  apply StatMech.Walls.rc71_witness_disjPreserving

/--
[rc71_witness_card_preserved](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc71disjpreserving.lean)
-/
@[path]
private lemma rc71_witness_card_preserved_eq
  {n : ℕ} :
-- imply
  (rc71_disjPreservingCompress 0 (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅})).card = (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅}).card := by
-- proof
  apply StatMech.Walls.rc71_witness_card_preserved

/--
[rc71_witness_compressed_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc71disjpreserving.lean)
-/
@[path]
private lemma rc71_witness_compressed_eq_eq
  {n : ℕ} :
-- imply
  rc71_disjPreservingCompress 0 (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅}) = ({{Sum.inl 0}, {Sum.inr 0}} : Finset (Finset (Fin 2 ⊕ Fin 2))) := by
-- proof
  apply StatMech.Walls.rc71_witness_compressed_eq

/--
[rc71_dbl_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc71disjpreserving.lean)
-/
@[path]
private lemma rc71_dbl_left_eq
  {n : ℕ} :
-- imply
  StatMech.dbl ({0} : Finset (Fin 2)) ∅ = ({Sum.inl 0} : Finset (Fin 2 ⊕ Fin 2)) := by
-- proof
  apply StatMech.Walls.rc71_dbl_left

/--
[rc71_dbl_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc71disjpreserving.lean)
-/
@[path]
private lemma rc71_dbl_right_eq
  {n : ℕ} :
-- imply
  StatMech.dbl (∅ : Finset (Fin 2)) {0} = ({Sum.inr 0} : Finset (Fin 2 ⊕ Fin 2)) := by
-- proof
  apply StatMech.Walls.rc71_dbl_right

/--
[rc71_dbl_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc71disjpreserving.lean)
-/
@[path]
private lemma rc71_dbl_empty_eq
  {n : ℕ} :
-- imply
  StatMech.dbl (∅ : Finset (Fin 2)) ∅ = (∅ : Finset (Fin 2 ⊕ Fin 2)) := by
-- proof
  apply StatMech.Walls.rc71_dbl_empty

/--
[rc71_empty_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc71disjpreserving.lean)
-/
@[path]
private lemma rc71_empty_notMem_eq
  {n : ℕ} :
-- imply
  (∅ : Finset (Fin 2 ⊕ Fin 2)) ∉ ({{Sum.inl 0}, {Sum.inr 0}} : Finset (Finset (Fin 2 ⊕ Fin 2))) := by
-- proof
  apply StatMech.Walls.rc71_empty_notMem

/--
[rc71_disjPreserving_not_boxDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc71disjpreserving.lean)
-/
@[path]
private lemma rc71_disjPreserving_not_boxDoubled_eq
  {n : ℕ} :
-- imply
  rc70_DisjPreserving 2 ({{Sum.inl 0}, {Sum.inr 0}} : Finset (Finset (Fin 2 ⊕ Fin 2))) ∧ ¬ rc71_IsBoxDoubled ({{Sum.inl 0}, {Sum.inr 0}} : Finset (Finset (Fin 2 ⊕ Fin 2))) := by
-- proof
  apply StatMech.Walls.rc71_disjPreserving_not_boxDoubled

/--
[rc71_witness_not_boxDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc71disjpreserving.lean)
-/
@[path]
private lemma rc71_witness_not_boxDoubled_eq
  {n : ℕ} :
-- imply
  ¬ rc71_IsBoxDoubled (rc71_disjPreservingCompress 0 (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅})) := by
-- proof
  apply StatMech.Walls.rc71_witness_not_boxDoubled

/--
[rc71_resolveLeft_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc71disjpreserving.lean)
-/
@[path]
private lemma rc71_resolveLeft_card_le_eq
  {n : ℕ}
  {i : Fin n}
  {Fam : Finset (Finset (Fin n ⊕ Fin n))} :
-- imply
  (rc71_resolveLeft i Fam).card ≤ Fam.card := by
-- proof
  apply StatMech.Walls.rc71_resolveLeft_card_le i Fam

/--
[rc71_resolveMember_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc71disjpreserving.lean)
-/
@[path]
private lemma rc71_resolveMember_subset_eq
  {n : ℕ}
  {i : Fin n}
  {U : Finset (Fin n ⊕ Fin n)} :
-- imply
  rc71_resolveMember i U ⊆ U := by
-- proof
  apply StatMech.Walls.rc71_resolveMember_subset i U

/--
[rc71_resolveLeft_preserves_other](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc71disjpreserving.lean)
-/
@[path]
private lemma rc71_resolveLeft_preserves_other_eq
  {n : ℕ}
  {i j : Fin n}
  {Fam : Finset (Finset (Fin n ⊕ Fin n))}
-- given
  (h : ∀ U ∈ Fam, ¬ (Sum.inl j ∈ U ∧ Sum.inr j ∈ U)) :
-- imply
  ∀ V ∈ rc71_resolveLeft i Fam, ¬ (Sum.inl j ∈ V ∧ Sum.inr j ∈ V) := by
-- proof
  apply StatMech.Walls.rc71_resolveLeft_preserves_other i j Fam h

/--
[rc71_reimerWprobCore_of_boxUnionBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc71disjpreserving.lean)
-/
@[path]
private lemma rc71_reimerWprobCore_of_boxUnionBound_eq
  {n : ℕ}
-- given
  (h : rc60_BoxUnionBound) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc71_reimerWprobCore_of_boxUnionBound h

/--
[rc71_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc71disjpreserving.lean)
-/
@[path]
private lemma rc71_status_eq
  {n : ℕ} :
-- imply
  (∀ (m : ℕ) (i : Fin m) (Fam : Finset (Finset (Fin m ⊕ Fin m))), ∀ V ∈ rc71_resolveLeft i Fam, ¬ (Sum.inl i ∈ V ∧ Sum.inr i ∈ V)) ∧ (rc70_DisjPreserving 2 (rc71_disjPreservingCompress 0 (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅}))) ∧ ((rc71_disjPreservingCompress 0 (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅})).card = (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅}).card) ∧ (rc70_DisjPreserving 2 ({{Sum.inl 0}, {Sum.inr 0}} : Finset (Finset (Fin 2 ⊕ Fin 2))) ∧ ¬ rc71_IsBoxDoubled ({{Sum.inl 0}, {Sum.inr 0}} : Finset (Finset (Fin 2 ⊕ Fin 2)))) ∧ (∀ (m : ℕ) (i : Fin m) (Fam : Finset (Finset (Fin m ⊕ Fin m))), (rc71_resolveLeft i Fam).card ≤ Fam.card) ∧ (rc60_BoxUnionBound → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc71_status


-- created on 2026-10-23
