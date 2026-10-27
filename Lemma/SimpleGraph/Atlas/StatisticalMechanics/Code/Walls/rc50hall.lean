import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc50hall.Part3
open Finset StatMech StatMech.Walls


/--
[rc50_jointImage_inter_complKL](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc50hall.lean)
-/
@[path]
private lemma rc50_jointImage_inter_complKL_eq
  [Fintype α]
  [DecidableEq α]
  {S K L : Finset α} :
-- imply
  rc49_jointImage S K L ∩ (K ∪ L)ᶜ = S ∩ (K ∪ L)ᶜ := by
-- proof
  apply StatMech.Walls.rc50_jointImage_inter_complKL S K L

/--
[rc50_jointImage_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc50hall.lean)
-/
@[path]
private lemma rc50_jointImage_involutive_eq
  [Fintype α]
  [DecidableEq α]
  {S K L : Finset α}
-- given
  (hKL : Disjoint K L) :
-- imply
  rc49_jointImage (rc49_jointImage S K L) K L = S := by
-- proof
  apply StatMech.Walls.rc50_jointImage_involutive S K L hKL

/--
[rc50_jointImage_injective_of_fixed_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc50hall.lean)
-/
@[path]
private lemma rc50_jointImage_injective_of_fixed_witness_eq
  [Fintype α]
  [DecidableEq α]
  {K L : Finset α}
-- given
  (hKL : Disjoint K L) :
-- imply
  Function.Injective (fun S => rc49_jointImage S K L) := by
-- proof
  apply StatMech.Walls.rc50_jointImage_injective_of_fixed_witness K L hKL

/--
[rc50_jointImage_mem_neighbourhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc50hall.lean)
-/
@[path]
private lemma rc50_jointImage_mem_neighbourhood_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S K L : Finset α}
-- given
  (hKL : Disjoint K L)
  (hKA : ∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜)
  (hLB : ∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) :
-- imply
  rc49_jointImage S K L ∈ rc49_neighbourhood 𝒜 ℬ S := by
-- proof
  apply StatMech.Walls.rc50_jointImage_mem_neighbourhood hKL hKA hLB

/--
[rc50_block_hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc50hall.lean)
-/
@[path]
private lemma rc50_block_hall_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {W : Finset (Finset α)}
  {K L : Finset α}
-- given
  (hKL : Disjoint K L)
  (hW : ∀ S ∈ W, (∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜) ∧ (∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ)) :
-- imply
  #W ≤ #(W.biUnion (rc49_neighbourhood 𝒜 ℬ)) := by
-- proof
  apply StatMech.Walls.rc50_block_hall hKL hW

/--
[rc50_wall_of_injectiveSelection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc50hall.lean)
-/
@[path]
private lemma rc50_wall_of_injectiveSelection_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (h : rc50_InjectiveSelection 𝒜 ℬ) :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc50_wall_of_injectiveSelection h

/--
[rc50_hall_of_injectiveSelection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc50hall.lean)
-/
@[path]
private lemma rc50_hall_of_injectiveSelection_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (h : rc50_InjectiveSelection 𝒜 ℬ) :
-- imply
  rc49_HallCond 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc50_hall_of_injectiveSelection h

/--
[rc50_injectiveSelection_of_hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc50hall.lean)
-/
@[path]
private lemma rc50_injectiveSelection_of_hall_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (h : rc49_HallCond 𝒜 ℬ) :
-- imply
  rc50_InjectiveSelection 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc50_injectiveSelection_of_hall h

/--
[rc50_hall_iff_injectiveSelection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc50hall.lean)
-/
@[path]
private lemma rc50_hall_iff_injectiveSelection_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc49_HallCond 𝒜 ℬ ↔ rc50_InjectiveSelection 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc50_hall_iff_injectiveSelection 𝒜 ℬ

/--
[rc50_reimer_closes_of_injectiveSelectionAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc50hall.lean)
-/
@[path]
private lemma rc50_reimer_closes_of_injectiveSelectionAll_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc50_InjectiveSelectionAll) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc50_reimer_closes_of_injectiveSelectionAll h

/--
[rc50_injectiveSelectionAll_iff_hallDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc50hall.lean)
-/
@[path]
private lemma rc50_injectiveSelectionAll_iff_hallDoubled_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc50_InjectiveSelectionAll ↔ rc49_HallDoubled := by
-- proof
  apply StatMech.Walls.rc50_injectiveSelectionAll_iff_hallDoubled

/--
[rc50_box_residual_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc50hall.lean)
-/
@[path]
private lemma rc50_box_residual_eq_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc20_famCylBox rc48_A₂ rc48_B₂ = {(∅ : Finset (Fin 3))} := by
-- proof
  apply StatMech.Walls.rc50_box_residual_eq

/--
[rc50_injectiveSelection_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc50hall.lean)
-/
@[path]
private lemma rc50_injectiveSelection_residual_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc50_InjectiveSelection rc48_A₂ rc48_B₂ := by
-- proof
  apply StatMech.Walls.rc50_injectiveSelection_residual

/--
[rc50_hall_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc50hall.lean)
-/
@[path]
private lemma rc50_hall_residual_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc49_HallCond rc48_A₂ rc48_B₂ := by
-- proof
  apply StatMech.Walls.rc50_hall_residual

/--
[rc50_reimer_involution_and_selection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc50hall.lean)
-/
@[path]
private lemma rc50_reimer_involution_and_selection_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ (S K L : Finset (Fin 3)), Disjoint K L → rc49_jointImage (rc49_jointImage S K L) K L = S) ∧ (∀ (K L : Finset (Fin 3)), Disjoint K L → Function.Injective (fun S => rc49_jointImage S K L)) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), rc49_HallCond 𝒜 ℬ ↔ rc50_InjectiveSelection 𝒜 ℬ) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), rc50_InjectiveSelection 𝒜 ℬ → #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) ∧ (rc50_InjectiveSelectionAll ↔ rc49_HallDoubled) ∧ (rc50_InjectiveSelectionAll → rc18_CylBoxReflInter) ∧ rc50_InjectiveSelection rc48_A₂ rc48_B₂ ∧ rc49_HallCond rc48_A₂ rc48_B₂ := by
-- proof
  apply StatMech.Walls.rc50_reimer_involution_and_selection


-- created on 2026-10-23
