import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc21persupport.Part5
open Finset StatMech StatMech.Walls


/--
[rc21_mem_famCylBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc21persupport.lean)
-/
@[path]
private lemma rc21_mem_famCylBox_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S : Finset α} :
-- imply
  S ∈ rc20_famCylBox 𝒜 ℬ ↔ ∃ K L : Finset α, Disjoint K L ∧ (∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜) ∧ (∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) := by
-- proof
  apply StatMech.Walls.rc21_mem_famCylBox 𝒜 ℬ S

/--
[rc21_symmDiff_inter_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc21persupport.lean)
-/
@[path]
private lemma rc21_symmDiff_inter_left_eq
  [Fintype α]
  [DecidableEq α]
  {S K L : Finset α}
-- given
  (hKL : Disjoint K L) :
-- imply
  (symmDiff S L) ∩ K = S ∩ K := by
-- proof
  apply StatMech.Walls.rc21_symmDiff_inter_left S K L hKL

/--
[rc21_symmDiff_compl_inter_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc21persupport.lean)
-/
@[path]
private lemma rc21_symmDiff_compl_inter_right_eq
  [Fintype α]
  [DecidableEq α]
  {S L : Finset α} :
-- imply
  (symmDiff S L)ᶜ ∩ L = S ∩ L := by
-- proof
  apply StatMech.Walls.rc21_symmDiff_compl_inter_right S L

/--
[rc21_symmDiff_mem_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc21persupport.lean)
-/
@[path]
private lemma rc21_symmDiff_mem_reflInter_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S K L : Finset α}
-- given
  (hKL : Disjoint K L)
  (hKA : ∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜)
  (hLB : ∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) :
-- imply
  symmDiff S L ∈ rc10_reflInter 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc21_symmDiff_mem_reflInter hKL hKA hLB

/--
[rc21_perSupportReflection_of_symmDiffReflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc21persupport.lean)
-/
@[path]
private lemma rc21_perSupportReflection_of_symmDiffReflection_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc21_SymmDiffReflection) :
-- imply
  rc20_PerSupportReflection := by
-- proof
  apply StatMech.Walls.rc21_perSupportReflection_of_symmDiffReflection h

/--
[rc21_cylBoxReflInter_of_symmDiffReflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc21persupport.lean)
-/
@[path]
private lemma rc21_cylBoxReflInter_of_symmDiffReflection_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc21_SymmDiffReflection) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc21_cylBoxReflInter_of_symmDiffReflection h

/--
[rc21_localRefl_mem_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc21persupport.lean)
-/
@[path]
private lemma rc21_localRefl_mem_reflInter_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S K L R : Finset α}
-- given
  (hKA : ∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜)
  (hLB : ∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ)
  (hRK : R ∩ K = S ∩ K)
  (hRL : Rᶜ ∩ L = S ∩ L) :
-- imply
  R ∈ rc10_reflInter 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc21_localRefl_mem_reflInter hKA hLB hRK hRL

/--
[rc21_boxComp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc21persupport.lean)
-/
@[path]
private lemma rc21_boxComp_eq_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))} :
-- imply
  rc21_boxComp n 𝒜 ℬ = rc20_famCylBox 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc21_boxComp_eq n 𝒜 ℬ

/--
[rc21_admComp_subset_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc21persupport.lean)
-/
@[path]
private lemma rc21_admComp_subset_reflInter_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)} :
-- imply
  rc21_admComp n 𝒜 ℬ S ⊆ rc10_reflInter 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc21_admComp_subset_reflInter n 𝒜 ℬ S

/--
[rc21_localReflSearch_fin2_refuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc21persupport.lean)
-/
@[path]
private lemma rc21_localReflSearch_fin2_refuted_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc21_localReflSearch 2 ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({{0}, {1}, {0, 1}} : Finset (Finset (Fin 2))) = false := by
-- proof
  apply StatMech.Walls.rc21_localReflSearch_fin2_refuted

/--
[rc21_symmDiffMirror_fin2_refuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc21persupport.lean)
-/
@[path]
private lemma rc21_symmDiffMirror_fin2_refuted_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ((rc21_boxComp 2 ({∅, {0}, {1}}) ({{0}, {1}, {0, 1}})).biUnion (fun S => (rc21_symmWitComp 2 ({∅, {0}, {1}}) ({{0}, {1}, {0, 1}}) S).image (fun L => symmDiff S L))).card < (rc21_boxComp 2 ({∅, {0}, {1}}) ({{0}, {1}, {0, 1}})).card := by
-- proof
  apply StatMech.Walls.rc21_symmDiffMirror_fin2_refuted

/--
[rc21_wall_holds_refuting_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc21persupport.lean)
-/
@[path]
private lemma rc21_wall_holds_refuting_pair_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({{0}, {1}, {0, 1}})) ≤ #(rc10_reflInter ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({{0}, {1}, {0, 1}})) := by
-- proof
  apply StatMech.Walls.rc21_wall_holds_refuting_pair

/--
[rc21_generalReflection_refuting_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc21persupport.lean)
-/
@[path]
private lemma rc21_generalReflection_refuting_pair_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∃ f : Finset (Fin 2) → Finset (Fin 2), Set.InjOn f (rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({{0}, {1}, {0, 1}}) : Set (Finset (Fin 2))) ∧ ∀ S ∈ rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({{0}, {1}, {0, 1}}), f S ∈ rc10_reflInter ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({{0}, {1}, {0, 1}}) := by
-- proof
  apply StatMech.Walls.rc21_generalReflection_refuting_pair

/--
[rc21_reimer_persupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc21persupport.lean)
-/
@[path]
private lemma rc21_reimer_persupport_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc21_SymmDiffReflection → rc18_CylBoxReflInter) ∧ (∀ {𝒜 ℬ : Finset (Finset α)} {S K L : Finset α}, Disjoint K L → (∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜) → (∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) → symmDiff S L ∈ rc10_reflInter 𝒜 ℬ) ∧ (rc21_localReflSearch 2 ({∅, {0}, {1}}) ({{0}, {1}, {0, 1}}) = false) ∧ (#(rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({{0}, {1}, {0, 1}})) ≤ #(rc10_reflInter ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({{0}, {1}, {0, 1}}))) := by
-- proof
  apply StatMech.Walls.rc21_reimer_persupport


-- created on 2026-10-23
