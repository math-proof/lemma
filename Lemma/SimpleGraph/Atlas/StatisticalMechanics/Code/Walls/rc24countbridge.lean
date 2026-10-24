import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc24countbridge
open Finset StatMech StatMech.Walls


/--
[rc24_traceCond_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc24countbridge.lean)
-/
@[path]
private lemma rc24_traceCond_antitone_eq
  [Fintype α]
  [DecidableEq α]
  {K₁ K₂ S T : Finset α}
-- given
  (h : K₁ ⊆ K₂)
  (hT : T ∩ K₂ = S ∩ K₂) :
-- imply
  T ∩ K₁ = S ∩ K₁ := by
-- proof
  apply StatMech.Walls.rc24_traceCond_antitone h hT

/--
[rc24_mem_complCylBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc24countbridge.lean)
-/
@[path]
private lemma rc24_mem_complCylBox_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S : Finset α} :
-- imply
  S ∈ rc24_complCylBox 𝒜 ℬ ↔ ∃ K : Finset α, (∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜) ∧ (∀ T : Finset α, T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ) := by
-- proof
  apply StatMech.Walls.rc24_mem_complCylBox 𝒜 ℬ S

/--
[rc24_complCylBox_subset_famCylBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc24countbridge.lean)
-/
@[path]
private lemma rc24_complCylBox_subset_famCylBox_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc24_complCylBox 𝒜 ℬ ⊆ rc20_famCylBox 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc24_complCylBox_subset_famCylBox 𝒜 ℬ

/--
[rc24_famCylBox_subset_complCylBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc24countbridge.lean)
-/
@[path]
private lemma rc24_famCylBox_subset_complCylBox_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc20_famCylBox 𝒜 ℬ ⊆ rc24_complCylBox 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc24_famCylBox_subset_complCylBox 𝒜 ℬ

/--
[rc24_famCylBox_eq_complCylBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc24countbridge.lean)
-/
@[path]
private lemma rc24_famCylBox_eq_complCylBox_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc20_famCylBox 𝒜 ℬ = rc24_complCylBox 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc24_famCylBox_eq_complCylBox 𝒜 ℬ

/--
[rc24_upComp_eq_complConj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc24countbridge.lean)
-/
@[path]
private lemma rc24_upComp_eq_complConj_eq
  [Fintype α]
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  rc22_upComp i 𝒜 = (Down.compression i (𝒜.image compl)).image compl := by
-- proof
  apply StatMech.Walls.rc24_upComp_eq_complConj i 𝒜

/--
[rc24_upCompComp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc24countbridge.lean)
-/
@[path]
private lemma rc24_upCompComp_eq_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {i : Fin n}
  {𝒜 : Finset (Finset (Fin n))} :
-- imply
  rc24_upCompComp n i 𝒜 = rc22_upComp i 𝒜 := by
-- proof
  apply StatMech.Walls.rc24_upCompComp_eq n i 𝒜

/--
[rc24_boxDownUpMono_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc24countbridge.lean)
-/
@[path]
private lemma rc24_boxDownUpMono_fin2_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 2))}
  {i : Fin 2} :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc20_famCylBox (Down.compression i 𝒜) (rc22_upComp i ℬ)) := by
-- proof
  apply StatMech.Walls.rc24_boxDownUpMono_fin2 𝒜 ℬ i

/--
[rc24_reflInter_downUp_increases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc24countbridge.lean)
-/
@[path]
private lemma rc24_reflInter_downUp_increases_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc10_reflInter ({∅} : Finset (Finset (Fin 2))) ({{0}})) < #(rc10_reflInter (Down.compression 1 ({∅} : Finset (Finset (Fin 2)))) (rc22_upComp 1 ({{0}} : Finset (Finset (Fin 2))))) := by
-- proof
  apply StatMech.Walls.rc24_reflInter_downUp_increases

/--
[rc24_famCylBox_violates_fiberRecursion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc24countbridge.lean)
-/
@[path]
private lemma rc24_famCylBox_violates_fiberRecursion_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc20_famCylBox ({∅} : Finset (Finset (Fin 2))) (univ)) ≠ #(rc20_famCylBox (({∅} : Finset (Finset (Fin 2))).nonMemberSubfamily 0) ((univ : Finset (Finset (Fin 2))).nonMemberSubfamily 0)) + #(rc20_famCylBox (({∅} : Finset (Finset (Fin 2))).memberSubfamily 0) ((univ : Finset (Finset (Fin 2))).nonMemberSubfamily 0)) + #(rc20_famCylBox (({∅} : Finset (Finset (Fin 2))).nonMemberSubfamily 0) ((univ : Finset (Finset (Fin 2))).memberSubfamily 0)) := by
-- proof
  apply StatMech.Walls.rc24_famCylBox_violates_fiberRecursion

/--
[rc24_reimer_countbridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc24countbridge.lean)
-/
@[path]
private lemma rc24_reimer_countbridge_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ (𝒜 ℬ : Finset (Finset α)), rc20_famCylBox 𝒜 ℬ = rc24_complCylBox 𝒜 ℬ) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 2))) (i : Fin 2), #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc20_famCylBox (Down.compression i 𝒜) (rc22_upComp i ℬ))) ∧ (#(rc10_reflInter ({∅} : Finset (Finset (Fin 2))) ({{0}})) < #(rc10_reflInter (Down.compression 1 ({∅} : Finset (Finset (Fin 2)))) (rc22_upComp 1 ({{0}} : Finset (Finset (Fin 2)))))) ∧ (#(rc20_famCylBox ({∅} : Finset (Finset (Fin 2))) (univ)) ≠ #(rc20_famCylBox (({∅} : Finset (Finset (Fin 2))).nonMemberSubfamily 0) ((univ : Finset (Finset (Fin 2))).nonMemberSubfamily 0)) + #(rc20_famCylBox (({∅} : Finset (Finset (Fin 2))).memberSubfamily 0) ((univ : Finset (Finset (Fin 2))).nonMemberSubfamily 0)) + #(rc20_famCylBox (({∅} : Finset (Finset (Fin 2))).nonMemberSubfamily 0) ((univ : Finset (Finset (Fin 2))).memberSubfamily 0))) := by
-- proof
  apply StatMech.Walls.rc24_reimer_countbridge


-- created on 2026-10-23
