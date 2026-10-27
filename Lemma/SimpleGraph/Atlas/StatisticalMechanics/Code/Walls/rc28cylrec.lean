import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc28cylrec.Part4
open Finset StatMech StatMech.Walls


/--
[rc28_mem_famCylBoxE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc28cylrec.lean)
-/
@[path]
private lemma rc28_mem_famCylBoxE_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 ℬ : Finset (Finset α)}
  {S : Finset α} :
-- imply
  S ∈ rc28_famCylBoxE E 𝒜 ℬ ↔ S ⊆ E ∧ ∃ K L : Finset α, Disjoint K L ∧ (∀ T : Finset α, T ⊆ E → T ∩ K = S ∩ K → T ∈ 𝒜) ∧ (∀ T : Finset α, T ⊆ E → T ∩ L = S ∩ L → T ∈ ℬ) := by
-- proof
  apply StatMech.Walls.rc28_mem_famCylBoxE E 𝒜 ℬ S

/--
[rc28_traceClassE_subset_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc28cylrec.lean)
-/
@[path]
private lemma rc28_traceClassE_subset_iff_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {E K S : Finset (Fin n)}
  {𝒜 : Finset (Finset (Fin n))} :
-- imply
  rc28_traceClassE n E K S ⊆ 𝒜 ↔ ∀ T : Finset (Fin n), T ⊆ E → T ∩ K = S ∩ K → T ∈ 𝒜 := by
-- proof
  apply StatMech.Walls.rc28_traceClassE_subset_iff n E K S 𝒜

/--
[rc28_traceCond_inter_ground](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc28cylrec.lean)
-/
@[path]
private lemma rc28_traceCond_inter_ground_eq
  [Fintype α]
  [DecidableEq α]
  {E K S T : Finset α}
-- given
  (hSE : S ⊆ E)
  (hTE : T ⊆ E) :
-- imply
  T ∩ (K ∩ E) = S ∩ (K ∩ E) ↔ T ∩ K = S ∩ K := by
-- proof
  apply StatMech.Walls.rc28_traceCond_inter_ground hSE hTE

/--
[rc28_famCylBoxEComp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc28cylrec.lean)
-/
@[path]
private lemma rc28_famCylBoxEComp_eq_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {E : Finset (Fin n)}
  {𝒜 ℬ : Finset (Finset (Fin n))} :
-- imply
  rc28_famCylBoxEComp n E 𝒜 ℬ = rc28_famCylBoxE E 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc28_famCylBoxEComp_eq n E 𝒜 ℬ

/--
[rc28_famCylBoxE_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc28cylrec.lean)
-/
@[path]
private lemma rc28_famCylBoxE_univ_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc28_famCylBoxE univ 𝒜 ℬ = rc20_famCylBox 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc28_famCylBoxE_univ 𝒜 ℬ

/--
[rc28_notMem_fiber_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc28cylrec.lean)
-/
@[path]
private lemma rc28_notMem_fiber_subset_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 ℬ : Finset (Finset α)}
  {a : α}
  {S : Finset α}
-- given
  (hS : S ∈ rc28_famCylBoxE E 𝒜 ℬ)
  (haS : a ∉ S) :
-- imply
  S ∈ rc28_famCylBoxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a) := by
-- proof
  apply StatMech.Walls.rc28_notMem_fiber_subset hS haS

/--
[rc28_insert_trace_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc28cylrec.lean)
-/
@[path]
private lemma rc28_insert_trace_eq_eq
  [Fintype α]
  [DecidableEq α]
  {K S T : Finset α}
  {a : α}
-- given
  (haS : a ∈ S)
  (haT : a ∉ T)
  (h : T ∩ K.erase a = (S.erase a) ∩ K.erase a) :
-- imply
  (insert a T) ∩ K = S ∩ K := by
-- proof
  apply StatMech.Walls.rc28_insert_trace_eq haS haT h

/--
[rc28_mem_fiber_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc28cylrec.lean)
-/
@[path]
private lemma rc28_mem_fiber_subset_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 ℬ : Finset (Finset α)}
  {a : α}
  {S : Finset α}
-- given
  (hS : S ∈ rc28_famCylBoxE E 𝒜 ℬ)
  (haS : a ∈ S) :
-- imply
  S.erase a ∈ rc28_famCylBoxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a) := by
-- proof
  apply StatMech.Walls.rc28_mem_fiber_subset hS haS

/--
[rc28_sameSideRecursion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc28cylrec.lean)
-/
@[path]
private lemma rc28_sameSideRecursion_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 ℬ : Finset (Finset α)}
  {a : α}
-- given
  (haE : a ∈ E) :
-- imply
  #(rc28_famCylBoxE E 𝒜 ℬ) ≤ #(rc28_famCylBoxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a)) + #(rc28_famCylBoxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a)) := by
-- proof
  apply StatMech.Walls.rc28_sameSideRecursion 𝒜 ℬ haE

/--
[rc28_reflEComp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc28cylrec.lean)
-/
@[path]
private lemma rc28_reflEComp_eq_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {E : Finset (Fin n)}
  {𝒜 ℬ : Finset (Finset (Fin n))} :
-- imply
  rc28_reflEComp n E 𝒜 ℬ = rc14_reflE E 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc28_reflEComp_eq n E 𝒜 ℬ

/--
[rc28_crossRecursion_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc28cylrec.lean)
-/
@[path]
private lemma rc28_crossRecursion_false_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ (#(rc28_famCylBoxE (univ : Finset (Fin 3)) ({∅, {0}, {1}, {2}, {0, 1}}) ({∅, {0}, {1}, {0, 1}, {0, 2}})) ≤ #(rc28_famCylBoxE ((univ : Finset (Fin 3)).erase 0) (({∅, {0}, {1}, {2}, {0, 1}} : Finset (Finset (Fin 3))).nonMemberSubfamily 0) (({∅, {0}, {1}, {0, 1}, {0, 2}} : Finset (Finset (Fin 3))).memberSubfamily 0)) + #(rc28_famCylBoxE ((univ : Finset (Fin 3)).erase 0) (({∅, {0}, {1}, {2}, {0, 1}} : Finset (Finset (Fin 3))).memberSubfamily 0) (({∅, {0}, {1}, {0, 1}, {0, 2}} : Finset (Finset (Fin 3))).nonMemberSubfamily 0))) := by
-- proof
  apply StatMech.Walls.rc28_crossRecursion_false

/--
[rc28_target_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc28cylrec.lean)
-/
@[path]
private lemma rc28_target_empty_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  #(rc28_famCylBoxE (∅ : Finset α) 𝒜 ℬ) ≤ #(rc14_reflE (∅ : Finset α) 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc28_target_empty 𝒜 ℬ

/--
[rc28_target_of_crossRecursion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc28cylrec.lean)
-/
@[path]
private lemma rc28_target_of_crossRecursion_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc28_CrossRecursion (α := α)) :
-- imply
  ∀ E : Finset α, ∀ 𝒜 ℬ : Finset (Finset α), #(rc28_famCylBoxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc28_target_of_crossRecursion h

/--
[rc28_box_le_sameSide_reflSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc28cylrec.lean)
-/
@[path]
private lemma rc28_box_le_sameSide_reflSum_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 ℬ : Finset (Finset α)}
  {a : α}
-- given
  (haE : a ∈ E)
  (hIHnn : #(rc28_famCylBoxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a)) ≤ #(rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a)))
  (hIHmm : #(rc28_famCylBoxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a)) ≤ #(rc14_reflE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a))) :
-- imply
  #(rc28_famCylBoxE E 𝒜 ℬ) ≤ #(rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a)) + #(rc14_reflE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a)) := by
-- proof
  apply StatMech.Walls.rc28_box_le_sameSide_reflSum 𝒜 ℬ haE hIHnn hIHmm

/--
[rc28_sameSide_reflSum_overshoots](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc28cylrec.lean)
-/
@[path]
private lemma rc28_sameSide_reflSum_overshoots_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc14_reflE (univ : Finset (Fin 3)) ({∅}) ({{1, 2}})) < #(rc28_reflEComp 3 ((univ : Finset (Fin 3)).erase 0) (({∅} : Finset (Finset (Fin 3))).nonMemberSubfamily 0) (({{1, 2}} : Finset (Finset (Fin 3))).nonMemberSubfamily 0)) + #(rc28_reflEComp 3 ((univ : Finset (Fin 3)).erase 0) (({∅} : Finset (Finset (Fin 3))).memberSubfamily 0) (({{1, 2}} : Finset (Finset (Fin 3))).memberSubfamily 0)) := by
-- proof
  apply StatMech.Walls.rc28_sameSide_reflSum_overshoots

/--
[rc28_sameSideRecursion_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc28cylrec.lean)
-/
@[path]
private lemma rc28_sameSideRecursion_witness_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc28_famCylBoxE (univ : Finset (Fin 3)) ({∅, {0}, {0, 1}, {1}}) ({∅, {0}, {0, 2}, {2}})) = 2 ∧ #(rc28_famCylBoxE ((univ : Finset (Fin 3)).erase 0) (({∅, {0}, {0, 1}, {1}} : Finset (Finset (Fin 3))).nonMemberSubfamily 0) (({∅, {0}, {0, 2}, {2}} : Finset (Finset (Fin 3))).nonMemberSubfamily 0)) = 1 ∧ #(rc28_famCylBoxE ((univ : Finset (Fin 3)).erase 0) (({∅, {0}, {0, 1}, {1}} : Finset (Finset (Fin 3))).memberSubfamily 0) (({∅, {0}, {0, 2}, {2}} : Finset (Finset (Fin 3))).memberSubfamily 0)) = 1 := by
-- proof
  apply StatMech.Walls.rc28_sameSideRecursion_witness

/--
[rc28_famCylBoxResidue_of_crossRecursion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc28cylrec.lean)
-/
@[path]
private lemma rc28_famCylBoxResidue_of_crossRecursion_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : ∀ {β : Type} [Fintype β] [DecidableEq β], rc28_CrossRecursion (α := β)) :
-- imply
  rc20_FamCylBoxResidue := by
-- proof
  apply StatMech.Walls.rc28_famCylBoxResidue_of_crossRecursion h

/--
[rc28_reimer_cylrec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc28cylrec.lean)
-/
@[path]
private lemma rc28_reimer_cylrec_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ (𝒜 ℬ : Finset (Finset α)), rc28_famCylBoxE univ 𝒜 ℬ = rc20_famCylBox 𝒜 ℬ) ∧ (∀ (E : Finset α) (𝒜 ℬ : Finset (Finset α)) (a : α), a ∈ E → #(rc28_famCylBoxE E 𝒜 ℬ) ≤ #(rc28_famCylBoxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a)) + #(rc28_famCylBoxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a))) ∧ (¬ (#(rc28_famCylBoxE (univ : Finset (Fin 3)) ({∅, {0}, {1}, {2}, {0, 1}}) ({∅, {0}, {1}, {0, 1}, {0, 2}})) ≤ #(rc28_famCylBoxE ((univ : Finset (Fin 3)).erase 0) (({∅, {0}, {1}, {2}, {0, 1}} : Finset (Finset (Fin 3))).nonMemberSubfamily 0) (({∅, {0}, {1}, {0, 1}, {0, 2}} : Finset (Finset (Fin 3))).memberSubfamily 0)) + #(rc28_famCylBoxE ((univ : Finset (Fin 3)).erase 0) (({∅, {0}, {1}, {2}, {0, 1}} : Finset (Finset (Fin 3))).memberSubfamily 0) (({∅, {0}, {1}, {0, 1}, {0, 2}} : Finset (Finset (Fin 3))).nonMemberSubfamily 0)))) ∧ (rc28_CrossRecursion (α := α) → ∀ E : Finset α, ∀ 𝒜 ℬ : Finset (Finset α), #(rc28_famCylBoxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 ℬ)) := by
-- proof
  apply StatMech.Walls.rc28_reimer_cylrec


-- created on 2026-10-23
