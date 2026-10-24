import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc49doubled
open Finset StatMech StatMech.Walls


/--
[rc49_jointImage_inter_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc49doubled.lean)
-/
@[path]
private lemma rc49_jointImage_inter_K_eq
  [Fintype α]
  [DecidableEq α]
  {S K L : Finset α}
-- given
  (hKL : Disjoint K L) :
-- imply
  rc49_jointImage S K L ∩ K = S ∩ K := by
-- proof
  apply StatMech.Walls.rc49_jointImage_inter_K S K L hKL

/--
[rc49_jointImage_compl_inter_L](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc49doubled.lean)
-/
@[path]
private lemma rc49_jointImage_compl_inter_L_eq
  [Fintype α]
  [DecidableEq α]
  {S K L : Finset α}
-- given
  (hKL : Disjoint K L) :
-- imply
  (rc49_jointImage S K L)ᶜ ∩ L = S ∩ L := by
-- proof
  apply StatMech.Walls.rc49_jointImage_compl_inter_L S K L hKL

/--
[rc49_jointImage_mem_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc49doubled.lean)
-/
@[path]
private lemma rc49_jointImage_mem_reflInter_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S K L : Finset α}
-- given
  (hKL : Disjoint K L)
  (hKA : ∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜)
  (hLB : ∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) :
-- imply
  rc49_jointImage S K L ∈ rc10_reflInter 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc49_jointImage_mem_reflInter hKL hKA hLB

/--
[rc49_neighbourhood_subset_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc49doubled.lean)
-/
@[path]
private lemma rc49_neighbourhood_subset_reflInter_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S : Finset α} :
-- imply
  rc49_neighbourhood 𝒜 ℬ S ⊆ rc10_reflInter 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc49_neighbourhood_subset_reflInter 𝒜 ℬ S

/--
[rc49_neighbourhood_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc49doubled.lean)
-/
@[path]
private lemma rc49_neighbourhood_nonempty_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S : Finset α}
-- given
  (hS : S ∈ rc20_famCylBox 𝒜 ℬ) :
-- imply
  (rc49_neighbourhood 𝒜 ℬ S).Nonempty := by
-- proof
  apply StatMech.Walls.rc49_neighbourhood_nonempty hS

/--
[rc49_wall_of_hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc49doubled.lean)
-/
@[path]
private lemma rc49_wall_of_hall_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (h : rc49_HallCond 𝒜 ℬ) :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc49_wall_of_hall 𝒜 ℬ h

/--
[rc49_reimer_closes_of_hallDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc49doubled.lean)
-/
@[path]
private lemma rc49_reimer_closes_of_hallDoubled_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc49_HallDoubled) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc49_reimer_closes_of_hallDoubled h

/--
[rc49_jointImage_residual_maps_empty_to_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc49doubled.lean)
-/
@[path]
private lemma rc49_jointImage_residual_maps_empty_to_zero_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc49_jointImage (∅ : Finset (Fin 3)) ({1, 2} : Finset (Fin 3)) ({0} : Finset (Fin 3)) = ({0} : Finset (Fin 3)) := by
-- proof
  apply StatMech.Walls.rc49_jointImage_residual_maps_empty_to_zero

/--
[rc49_residual_KcylA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc49doubled.lean)
-/
@[path]
private lemma rc49_residual_KcylA_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∀ T : Finset (Fin 3), T ∩ ({1, 2} : Finset (Fin 3)) = (∅ : Finset (Fin 3)) ∩ {1, 2} → T ∈ rc48_A₂ := by
-- proof
  apply StatMech.Walls.rc49_residual_KcylA

/--
[rc49_residual_LcylB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc49doubled.lean)
-/
@[path]
private lemma rc49_residual_LcylB_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∀ T : Finset (Fin 3), T ∩ ({0} : Finset (Fin 3)) = (∅ : Finset (Fin 3)) ∩ {0} → T ∈ rc48_B₂ := by
-- proof
  apply StatMech.Walls.rc49_residual_LcylB

/--
[rc49_residual_target_mem_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc49doubled.lean)
-/
@[path]
private lemma rc49_residual_target_mem_reflInter_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ({0} : Finset (Fin 3)) ∈ rc10_reflInter rc48_A₂ rc48_B₂ := by
-- proof
  apply StatMech.Walls.rc49_residual_target_mem_reflInter

/--
[rc49_residual_neighbourhood_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc49doubled.lean)
-/
@[path]
private lemma rc49_residual_neighbourhood_nonempty_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc49_neighbourhood rc48_A₂ rc48_B₂ (∅ : Finset (Fin 3))).Nonempty := by
-- proof
  apply StatMech.Walls.rc49_residual_neighbourhood_nonempty

/--
[rc49_wall_residual_holds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc49doubled.lean)
-/
@[path]
private lemma rc49_wall_residual_holds_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc20_famCylBoxComp 3 rc48_A₂ rc48_B₂).card ≤ (rc20_reflInterComp 3 rc48_A₂ rc48_B₂).card := by
-- proof
  apply StatMech.Walls.rc49_wall_residual_holds

/--
[rc49_reimer_joint_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc49doubled.lean)
-/
@[path]
private lemma rc49_reimer_joint_witness_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ (𝒜 ℬ : Finset (Finset (Fin 3))) (S K L : Finset (Fin 3)), Disjoint K L → (∀ T : Finset (Fin 3), T ∩ K = S ∩ K → T ∈ 𝒜) → (∀ T : Finset (Fin 3), T ∩ L = S ∩ L → T ∈ ℬ) → rc49_jointImage S K L ∈ rc10_reflInter 𝒜 ℬ) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))) (S : Finset (Fin 3)), S ∈ rc20_famCylBox 𝒜 ℬ → (rc49_neighbourhood 𝒜 ℬ S).Nonempty) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), rc49_HallCond 𝒜 ℬ → #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) ∧ (rc49_HallDoubled → rc18_CylBoxReflInter) ∧ (rc49_jointImage (∅ : Finset (Fin 3)) ({1, 2}) ({0}) = ({0} : Finset (Fin 3))) ∧ (({0} : Finset (Fin 3)) ∈ rc10_reflInter rc48_A₂ rc48_B₂) ∧ ((rc20_famCylBoxComp 3 rc48_A₂ rc48_B₂).card ≤ (rc20_reflInterComp 3 rc48_A₂ rc48_B₂).card) := by
-- proof
  apply StatMech.Walls.rc49_reimer_joint_witness


-- created on 2026-10-23
