import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SetFamily.TuranSystem
import Lemma.Finset.SetFamily.TuranSystem
open TuranSystem


/--
[valid_332](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma valid_332
-- imply
  IsTuranSystem 3 3 2 (completeGraph 3 2) :=
-- proof
  completeGraph_isTuran 3 3 2 ⟨by decide, by decide, by decide⟩

/--
[valid_s_lt_n](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma valid_s_lt_n
-- imply
  IsTuranSystem 4 3 2 (completeGraph 4 2) :=
-- proof
  completeGraph_isTuran 4 3 2 ⟨by decide, by decide, by decide⟩

/--
[uniform_direct](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma uniform_direct
-- imply
  SetFamily.IsUniform (completeGraph 3 2) 2 :=
-- proof
  completeGraph_uniform 3 2

/--
[uniform_iff_use](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma uniform_iff_use
-- imply
  SetFamily.IsUniform (completeGraph 3 2) 2 ↔ ∀ e ∈ completeGraph 3 2, e.card = 2 :=
-- proof
  SetFamily.isUniform_iff (completeGraph 3 2) 2

/--
[uniform_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma uniform_explicit
-- imply
  SetFamily.IsUniform ({({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))) 2 := by
-- proof
  refine (SetFamily.isUniform_iff _ _).mpr ?_
  decide

/--
[reject_empty_uncovered](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma reject_empty_uncovered
-- imply
  ¬ IsTuranSystem 3 3 2 ∅ := by
-- proof
  intro h
  have hcov := cover_of_isTuran 3 3 2 _ h
  have hT : (Finset.univ : Finset (Fin 3)) ∈
    Finset.powersetCard 3 (Finset.univ : Finset (Fin 3)) :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by decide⟩
  obtain ⟨e, he, _⟩ := hcov _ hT
  simp at he

/--
[reject_wrong_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma reject_wrong_card
-- imply
  ¬ IsTuranSystem 3 3 2 ({({0} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by
-- proof
  intro h
  have hu := uniform_of_isTuran 3 3 2 _ h
  have hmem :
    ({0} : Finset (Fin 3)) ∈
      ({({0} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by simp
  have h2 := hu _ hmem
  have h1 : ({0} : Finset (Fin 3)).card = 1 := by decide
  omega

/--
[direction_edge_sub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma direction_edge_sub
-- imply
  ∃ e ∈ completeGraph 4 2, e ⊆ ({0, 1, 2} : Finset (Fin 4)) ∧ ¬ ({0, 1, 2} : Finset (Fin 4)) ⊆ e := by
-- proof
  refine ⟨({0, 1} : Finset (Fin 4)), ?_, ?_, ?_⟩
  · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by decide⟩
  · decide
  · decide

/--
[reject_r_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma reject_r_zero
-- imply
  ¬ IsTuranSystem 3 3 0 (completeGraph 3 0) := by
-- proof
  intro h
  have hpos := pos_of_isTuran 3 3 0 _ h
  omega

/--
[reject_r_ge_s](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma reject_r_ge_s
-- imply
  ¬ IsTuranSystem 3 2 2 (completeGraph 3 2) := by
-- proof
  intro h
  have hlt := lt_of_isTuran 3 2 2 _ h
  omega

/--
[reject_r_gt_s](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma reject_r_gt_s
-- imply
  ¬ IsTuranSystem 3 2 3 (completeGraph 3 3) := by
-- proof
  intro h
  have hlt := lt_of_isTuran 3 2 3 _ h
  omega

/--
[reject_s_gt_n](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma reject_s_gt_n
-- imply
  ¬ IsTuranSystem 2 3 2 (completeGraph 2 2) := by
-- proof
  intro h
  have hle := le_of_isTuran 2 3 2 _ h
  omega

/--
[uncovered_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma uncovered_uniform
-- imply
  SetFamily.IsUniform ({({0, 1} : Finset (Fin 4))} : Finset (Finset (Fin 4))) 2 :=
-- proof
  (SetFamily.isUniform_iff _ _).mpr (by decide)

/--
[uncovered_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma uncovered_nonempty
-- imply
  ({({0, 1} : Finset (Fin 4))} : Finset (Finset (Fin 4))).Nonempty :=
-- proof
  Finset.singleton_nonempty _

/--
[reject_uncovered_only](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma reject_uncovered_only
-- imply
  ¬ IsTuranSystem 4 3 2 ({({0, 1} : Finset (Fin 4))} : Finset (Finset (Fin 4))) := by
-- proof
  intro h
  have hcov := cover_of_isTuran 4 3 2 _ h
  have hT : ({1, 2, 3} : Finset (Fin 4)) ∈
    Finset.powersetCard 3 (Finset.univ : Finset (Fin 4)) := by
    refine Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩
    decide
  obtain ⟨e, he, hsub⟩ := hcov _ hT
  have heq : e = ({0, 1} : Finset (Fin 4)) := by simpa using he
  rw [heq] at hsub
  have hfalse : ¬ (({0, 1} : Finset (Fin 4)) ⊆ ({1, 2, 3} : Finset (Fin 4))) := by
    decide
  exact hfalse hsub

/--
[realized_direct](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma realized_direct
-- imply
  (completeGraph 3 2).card ∈ realizedCounts 3 3 2 :=
-- proof
  (mem_realizedCounts 3 3 2 _).mpr ⟨completeGraph 3 2, valid_332, rfl⟩

/--
[exists_system_use](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma exists_system_use
-- imply
  ∃ H, IsTuranSystem 3 3 2 H :=
-- proof
  exists_system 3 3 2 ⟨by decide, by decide, by decide⟩

/--
[realized_nonempty_use](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma realized_nonempty_use
-- imply
  ∃ k, k ∈ realizedCounts 3 3 2 :=
-- proof
  realizedCounts_nonempty 3 3 2 ⟨by decide, by decide, by decide⟩

/--
[turan_mem_use](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma turan_mem_use
-- imply
  turanNumber 3 3 2 ∈ realizedCounts 3 3 2 :=
-- proof
  turanNumber_mem 3 3 2 ⟨by decide, by decide, by decide⟩

/--
[turan_attains_use](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma turan_attains_use
-- imply
  ∃ H, IsTuranSystem 3 3 2 H ∧ H.card = turanNumber 3 3 2 :=
-- proof
  turanNumber_attains 3 3 2 ⟨by decide, by decide, by decide⟩

/--
[turan_le_use](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma turan_le_use
-- imply
  turanNumber 3 3 2 ≤ (completeGraph 3 2).card :=
-- proof
  turanNumber_le 3 3 2 (completeGraph 3 2) valid_332

/--
[one_edge_valid](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma one_edge_valid
-- imply
  IsTuranSystem 3 3 2 ({({0, 1} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by
-- proof
  refine ⟨by decide, by decide, by decide, (SetFamily.isUniform_iff _ _).mpr (by decide), ?_⟩
  intro T hT
  have hTcard : T.card = 3 := (Finset.mem_powersetCard.mp hT).2
  have huniv : (Finset.univ : Finset (Fin 3)).card = 3 := by decide
  have hTsub : T ⊆ (Finset.univ : Finset (Fin 3)) :=
    (Finset.mem_powersetCard.mp hT).1
  have hle : (Finset.univ : Finset (Fin 3)).card ≤ T.card := by rw [hTcard, huniv]
  have hTeq : T = Finset.univ := Finset.eq_of_subset_of_card_le hTsub hle
  exact ⟨({0, 1} : Finset (Fin 3)), by simp, by rw [hTeq]; decide⟩

/--
[one_le_card_of_valid](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma one_le_card_of_valid
  {H : Finset (Finset (Fin 3))}
-- given
  (h : IsTuranSystem 3 3 2 H) :
-- imply
  1 ≤ H.card := by
-- proof
  by_contra hcon
  push Not at hcon
  have hzero : H.card = 0 := by omega
  have hempty : H = ∅ := Finset.card_eq_zero.mp hzero
  have hcov := cover_of_isTuran 3 3 2 H h
  have hT : (Finset.univ : Finset (Fin 3)) ∈
    Finset.powersetCard 3 (Finset.univ : Finset (Fin 3)) :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by decide⟩
  obtain ⟨e, he, _⟩ := hcov _ hT
  rw [hempty] at he
  simp at he

/--
[turan_lower_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma turan_lower_one
-- imply
  1 ≤ turanNumber 3 3 2 := by
-- proof
  refine le_turanNumber 3 3 2 1 ?_ ⟨by decide, by decide, by decide⟩
  intro k hk
  obtain ⟨H, hH, rfl⟩ := (mem_realizedCounts 3 3 2 k).mp hk
  exact one_le_card_of_valid H hH

/--
[turan_upper_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma turan_upper_one
-- imply
  turanNumber 3 3 2 ≤ 1 := by
-- proof
  have hle := turanNumber_le 3 3 2 _ one_edge_valid
  have hcard :
    ({({0, 1} : Finset (Fin 3))} : Finset (Finset (Fin 3))).card = 1 := by
    decide
  omega

/--
[turan_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/TuranSystem.lean)
-/
@[path]
lemma turan_eq_one
-- imply
  turanNumber 3 3 2 = 1 :=
-- proof
  Nat.le_antisymm turan_upper_one turan_lower_one


-- created on 2026-10-23
