import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc31doubledcover
open Finset StatMech StatMech.Walls


/--
[rc31_compl_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc31doubledcover.lean)
-/
@[path]
private lemma rc31_compl_involutive_eq
  [Fintype α]
  [DecidableEq α]
  {S : Finset α} :
-- imply
  Sᶜᶜ = S := by
-- proof
  apply StatMech.Walls.rc31_compl_involutive S

/--
[rc31_reflInter_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc31doubledcover.lean)
-/
@[path]
private lemma rc31_reflInter_swap_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  #(rc10_reflInter 𝒜 ℬ) = #(rc10_reflInter ℬ 𝒜) := by
-- proof
  apply StatMech.Walls.rc31_reflInter_swap 𝒜 ℬ

/--
[rc31_complPairs_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc31doubledcover.lean)
-/
@[path]
private lemma rc31_complPairs_swap_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  #(rc22_complPairs 𝒜 ℬ) = #(rc22_complPairs ℬ 𝒜) := by
-- proof
  apply StatMech.Walls.rc31_complPairs_swap 𝒜 ℬ

/--
[rc31_famCylBox_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc31doubledcover.lean)
-/
@[path]
private lemma rc31_famCylBox_swap_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc20_famCylBox 𝒜 ℬ = rc20_famCylBox ℬ 𝒜 := by
-- proof
  apply StatMech.Walls.rc31_famCylBox_swap 𝒜 ℬ

/--
[rc31_wall_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc31doubledcover.lean)
-/
@[path]
private lemma rc31_wall_symm_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) ↔ #(rc20_famCylBox ℬ 𝒜) ≤ #(rc10_reflInter ℬ 𝒜) := by
-- proof
  apply StatMech.Walls.rc31_wall_symm 𝒜 ℬ

/--
[rc31_boxWitness_to_complPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc31doubledcover.lean)
-/
@[path]
private lemma rc31_boxWitness_to_complPair_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S K L : Finset α}
-- given
  (hKL : Disjoint K L)
  (hKA : ∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜)
  (hLB : ∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) :
-- imply
  (symmDiff S L, (symmDiff S L)ᶜ) ∈ rc22_complPairs 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc31_boxWitness_to_complPair hKL hKA hLB

/--
[rc31_boxCompressionMono_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc31doubledcover.lean)
-/
@[path]
private lemma rc31_boxCompressionMono_false_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ (#(rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 3))) ({∅, {0}, {0, 1}, {2}, {0, 2}, {0, 1, 2}})) ≤ #(rc20_famCylBox (Down.compression 0 ({∅, {0}, {1}} : Finset (Finset (Fin 3)))) (Down.compression 0 ({∅, {0}, {0, 1}, {2}, {0, 2}, {0, 1, 2}})))) := by
-- proof
  apply StatMech.Walls.rc31_boxCompressionMono_false

/--
[rc31_not_boxCompressionMono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc31doubledcover.lean)
-/
@[path]
private lemma rc31_not_boxCompressionMono_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ rc22_BoxCompressionMono := by
-- proof
  apply StatMech.Walls.rc31_not_boxCompressionMono

/--
[rc31_wall_holds_on_boxDrop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc31doubledcover.lean)
-/
@[path]
private lemma rc31_wall_holds_on_boxDrop_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 3))) ({∅, {0}, {0, 1}, {2}, {0, 2}, {0, 1, 2}})) ≤ #(rc10_reflInter ({∅, {0}, {1}} : Finset (Finset (Fin 3))) ({∅, {0}, {0, 1}, {2}, {0, 2}, {0, 1, 2}})) := by
-- proof
  apply StatMech.Walls.rc31_wall_holds_on_boxDrop

/--
[rc31_famCylBoxResidue_of_perSupportReflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc31doubledcover.lean)
-/
@[path]
private lemma rc31_famCylBoxResidue_of_perSupportReflection_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc20_PerSupportReflection) :
-- imply
  rc20_FamCylBoxResidue := by
-- proof
  apply StatMech.Walls.rc31_famCylBoxResidue_of_perSupportReflection h

/--
[rc31_cylBoxReflInter_of_symmDiffReflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc31doubledcover.lean)
-/
@[path]
private lemma rc31_cylBoxReflInter_of_symmDiffReflection_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc21_SymmDiffReflection) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc31_cylBoxReflInter_of_symmDiffReflection h

/--
[rc31_boxDownsetBase_fin0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc31doubledcover.lean)
-/
@[path]
private lemma rc31_boxDownsetBase_fin0_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 0))} :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc31_boxDownsetBase_fin0 𝒜 ℬ

/--
[rc31_boxDownsetBase_upperSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc31doubledcover.lean)
-/
@[path]
private lemma rc31_boxDownsetBase_upperSet_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
-- given
  (h𝒜 : IsUpperSet (𝒜 : Set (Finset (Fin n))))
  (hℬ : IsUpperSet (ℬ : Set (Finset (Fin n)))) :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc31_boxDownsetBase_upperSet h𝒜 hℬ

/--
[rc31_reflInter_downDown_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc31doubledcover.lean)
-/
@[path]
private lemma rc31_reflInter_downDown_antitone_eq
  [Fintype α]
  [DecidableEq α]
  {i : α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  #(rc10_reflInter (Down.compression i 𝒜) (Down.compression i ℬ)) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc31_reflInter_downDown_antitone i 𝒜 ℬ

/--
[rc31_reimer_doubledcover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc31doubledcover.lean)
-/
@[path]
private lemma rc31_reimer_doubledcover_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ (𝒜 ℬ : Finset (Finset α)), #(rc10_reflInter 𝒜 ℬ) = #(rc10_reflInter ℬ 𝒜)) ∧ (∀ (𝒜 ℬ : Finset (Finset α)), rc20_famCylBox 𝒜 ℬ = rc20_famCylBox ℬ 𝒜) ∧ (∀ {𝒜 ℬ : Finset (Finset α)} {S K L : Finset α}, Disjoint K L → (∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜) → (∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) → (symmDiff S L, (symmDiff S L)ᶜ) ∈ rc22_complPairs 𝒜 ℬ) ∧ (¬ rc22_BoxCompressionMono) ∧ (#(rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 3))) ({∅, {0}, {0, 1}, {2}, {0, 2}, {0, 1, 2}})) ≤ #(rc10_reflInter ({∅, {0}, {1}} : Finset (Finset (Fin 3))) ({∅, {0}, {0, 1}, {2}, {0, 2}, {0, 1, 2}}))) ∧ (rc20_PerSupportReflection → rc20_FamCylBoxResidue) := by
-- proof
  apply StatMech.Walls.rc31_reimer_doubledcover


-- created on 2026-10-23
