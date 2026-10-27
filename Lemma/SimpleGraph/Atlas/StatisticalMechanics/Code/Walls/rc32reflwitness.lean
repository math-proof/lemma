import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc32reflwitness.Part2
open Finset StatMech StatMech.Walls


/--
[rc32_symmDiff_mem_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc32reflwitness.lean)
-/
@[path]
private lemma rc32_symmDiff_mem_reflInter_eq
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
  apply StatMech.Walls.rc32_symmDiff_mem_reflInter hKL hKA hLB

/--
[rc32_reimer_closes_of_perSupportReflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc32reflwitness.lean)
-/
@[path]
private lemma rc32_reimer_closes_of_perSupportReflection_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc20_PerSupportReflection) :
-- imply
  rc20_FamCylBoxResidue := by
-- proof
  apply StatMech.Walls.rc32_reimer_closes_of_perSupportReflection h

/--
[rc32_cylBoxReflInter_of_symmDiffReflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc32reflwitness.lean)
-/
@[path]
private lemma rc32_cylBoxReflInter_of_symmDiffReflection_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc21_SymmDiffReflection) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc32_cylBoxReflInter_of_symmDiffReflection h

/--
[rc32_box_card_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc32reflwitness.lean)
-/
@[path]
private lemma rc32_box_card_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc20_famCylBox rc32_A3 rc32_B3) = 2 := by
-- proof
  apply StatMech.Walls.rc32_box_card_fin3

/--
[rc32_reflInter_card_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc32reflwitness.lean)
-/
@[path]
private lemma rc32_reflInter_card_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc10_reflInter rc32_A3 rc32_B3) = 3 := by
-- proof
  apply StatMech.Walls.rc32_reflInter_card_fin3

/--
[rc32_wall_holds_on_fin3_refuter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc32reflwitness.lean)
-/
@[path]
private lemma rc32_wall_holds_on_fin3_refuter_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc20_famCylBox rc32_A3 rc32_B3) ≤ #(rc10_reflInter rc32_A3 rc32_B3) := by
-- proof
  apply StatMech.Walls.rc32_wall_holds_on_fin3_refuter

/--
[rc32_localReflSearch_fin3_refuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc32reflwitness.lean)
-/
@[path]
private lemma rc32_localReflSearch_fin3_refuted_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc21_localReflSearch 3 rc32_A3 rc32_B3 = false := by
-- proof
  apply StatMech.Walls.rc32_localReflSearch_fin3_refuted

/--
[rc32_symmDiffMirror_fin3_refuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc32reflwitness.lean)
-/
@[path]
private lemma rc32_symmDiffMirror_fin3_refuted_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ((rc21_boxComp 3 rc32_A3 rc32_B3).biUnion (fun S => (rc21_symmWitComp 3 rc32_A3 rc32_B3 S).image (fun L => symmDiff S L))).card < (rc21_boxComp 3 rc32_A3 rc32_B3).card := by
-- proof
  apply StatMech.Walls.rc32_symmDiffMirror_fin3_refuted

/--
[rc32_generalReflection_fin3_refuter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc32reflwitness.lean)
-/
@[path]
private lemma rc32_generalReflection_fin3_refuter_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∃ f : Finset (Fin 3) → Finset (Fin 3), Set.InjOn f (rc20_famCylBox rc32_A3 rc32_B3 : Set (Finset (Fin 3))) ∧ ∀ S ∈ rc20_famCylBox rc32_A3 rc32_B3, f S ∈ rc10_reflInter rc32_A3 rc32_B3 := by
-- proof
  apply StatMech.Walls.rc32_generalReflection_fin3_refuter

/--
[rc32_symmDiffReflection_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc32reflwitness.lean)
-/
@[path]
private lemma rc32_symmDiffReflection_false_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ rc21_SymmDiffReflection := by
-- proof
  apply StatMech.Walls.rc32_symmDiffReflection_false

/--
[rc32_reimer_reflwitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc32reflwitness.lean)
-/
@[path]
private lemma rc32_reimer_reflwitness_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ {𝒜 ℬ : Finset (Finset α)} {S K L : Finset α}, Disjoint K L → (∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜) → (∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) → symmDiff S L ∈ rc10_reflInter 𝒜 ℬ) ∧ (rc20_PerSupportReflection → rc20_FamCylBoxResidue) ∧ (#(rc20_famCylBox rc32_A3 rc32_B3) ≤ #(rc10_reflInter rc32_A3 rc32_B3)) ∧ (rc21_localReflSearch 3 rc32_A3 rc32_B3 = false) ∧ (¬ rc21_SymmDiffReflection) := by
-- proof
  apply StatMech.Walls.rc32_reimer_reflwitness


-- created on 2026-10-23
