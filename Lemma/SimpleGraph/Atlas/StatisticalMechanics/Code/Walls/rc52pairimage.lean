import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc52pairimage
open Finset StatMech StatMech.Walls


/--
[rc52_pairImage_left_eq_jointImage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc52pairimage.lean)
-/
@[path]
private lemma rc52_pairImage_left_eq_jointImage_eq
  [Fintype α]
  [DecidableEq α]
  {S K L : Finset α} :
-- imply
  (rc52_pairImage S K L).1 = rc49_jointImage S K L := by
-- proof
  apply StatMech.Walls.rc52_pairImage_left_eq_jointImage S K L

/--
[rc52_pairImage_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc52pairimage.lean)
-/
@[path]
private lemma rc52_pairImage_snd_eq
  [Fintype α]
  [DecidableEq α]
  {S K L : Finset α} :
-- imply
  (rc52_pairImage S K L).2 = (rc49_jointImage S K L)ᶜ := by
-- proof
  apply StatMech.Walls.rc52_pairImage_snd S K L

/--
[rc52_pairImage_mem_complPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc52pairimage.lean)
-/
@[path]
private lemma rc52_pairImage_mem_complPairs_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S K L : Finset α}
-- given
  (hKL : Disjoint K L)
  (hKA : ∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜)
  (hLB : ∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) :
-- imply
  rc52_pairImage S K L ∈ rc22_complPairs 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc52_pairImage_mem_complPairs hKL hKA hLB

/--
[rc52_pairImage_determined_by_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc52pairimage.lean)
-/
@[path]
private lemma rc52_pairImage_determined_by_left_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {p : Finset α × Finset α}
-- given
  (hp : p ∈ rc22_complPairs 𝒜 ℬ) :
-- imply
  p.1ᶜ = p.2 := by
-- proof
  apply StatMech.Walls.rc52_pairImage_determined_by_left hp

/--
[rc52_pairImage_injOn_iff_jointImage_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc52pairimage.lean)
-/
@[path]
private lemma rc52_pairImage_injOn_iff_jointImage_injOn_eq
  [Fintype α]
  [DecidableEq α]
  {K L : Finset α}
  {s : Set (Finset α)} :
-- imply
  Set.InjOn (fun S => rc52_pairImage S K L) s ↔ Set.InjOn (fun S => rc49_jointImage S K L) s := by
-- proof
  apply StatMech.Walls.rc52_pairImage_injOn_iff_jointImage_injOn K L s

/--
[rc52_pairImage_collapses_refuter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc52pairimage.lean)
-/
@[path]
private lemma rc52_pairImage_collapses_refuter_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc52_pairImage ({0} : Finset (Fin 3)) ({1, 2}) ({0}) = rc52_pairImage ({1} : Finset (Fin 3)) ({0, 2}) ({1}) ∧ rc52_pairImage ({0} : Finset (Fin 3)) ({1, 2}) ({0}) = (∅, (univ : Finset (Fin 3))) := by
-- proof
  apply StatMech.Walls.rc52_pairImage_collapses_refuter

/--
[rc52_decoupled_pair_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc52pairimage.lean)
-/
@[path]
private lemma rc52_decoupled_pair_bound_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {g : Finset α → Finset α × Finset α}
-- given
  (hinj : Set.InjOn g (rc20_famCylBox 𝒜 ℬ : Set (Finset α)))
  (hmem : ∀ S ∈ rc20_famCylBox 𝒜 ℬ, g S ∈ (rc10_reflInter 𝒜 ℬ) ×ˢ (rc10_reflInter 𝒜 ℬ)) :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ (#(rc10_reflInter 𝒜 ℬ)) ^ 2 := by
-- proof
  apply StatMech.Walls.rc52_decoupled_pair_bound hinj hmem

/--
[rc52_wall_refuter_holds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc52pairimage.lean)
-/
@[path]
private lemma rc52_wall_refuter_holds_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc20_famCylBoxComp 3 rc51_Aref rc51_Bref).card ≤ (rc20_reflInterComp 3 rc51_Aref rc51_Bref).card := by
-- proof
  apply StatMech.Walls.rc52_wall_refuter_holds

/--
[rc52_reimer_pair_route_hits_black_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc52pairimage.lean)
-/
@[path]
private lemma rc52_reimer_pair_route_hits_black_box_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ (𝒜 ℬ : Finset (Finset (Fin 3))) (S K L : Finset (Fin 3)), Disjoint K L → (∀ T : Finset (Fin 3), T ∩ K = S ∩ K → T ∈ 𝒜) → (∀ T : Finset (Fin 3), T ∩ L = S ∩ L → T ∈ ℬ) → rc52_pairImage S K L ∈ rc22_complPairs 𝒜 ℬ) ∧ (∀ (K L : Finset (Fin 3)) (s : Set (Finset (Fin 3))), Set.InjOn (fun S => rc52_pairImage S K L) s ↔ Set.InjOn (fun S => rc49_jointImage S K L) s) ∧ (rc52_pairImage ({0} : Finset (Fin 3)) ({1, 2}) ({0}) = rc52_pairImage ({1} : Finset (Fin 3)) ({0, 2}) ({1}) ∧ rc52_pairImage ({0} : Finset (Fin 3)) ({1, 2}) ({0}) = (∅, (univ : Finset (Fin 3)))) ∧ ((rc20_famCylBoxComp 3 rc51_Aref rc51_Bref).card ≤ (rc20_reflInterComp 3 rc51_Aref rc51_Bref).card) := by
-- proof
  apply StatMech.Walls.rc52_reimer_pair_route_hits_black_box


-- created on 2026-10-23
