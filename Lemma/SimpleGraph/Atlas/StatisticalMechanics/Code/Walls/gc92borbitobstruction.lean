import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc92borbitobstruction.Part2
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc92b_degK_perm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc92borbitobstruction.lean)
-/
@[path]
private lemma gc92b_degK_perm_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {τ : Equiv.Perm ι}
  {K : Finset ι}
  {w : W}
-- given
  (hτ : ∀ i, ends (τ i) = ends i) :
-- imply
  degK ends (K.image τ) w = degK ends K w := by
-- proof
  apply StatMech.Walls.gc92b_degK_perm ends τ hτ K w

/--
[gc92b_sources_perm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc92borbitobstruction.lean)
-/
@[path]
private lemma gc92b_sources_perm_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {τ : Equiv.Perm ι}
  {K : Finset ι}
-- given
  (hτ : ∀ i, ends (τ i) = ends i) :
-- imply
  sources ends (K.image τ) = sources ends K := by
-- proof
  apply StatMech.Walls.gc92b_sources_perm ends τ hτ K

/--
[gc92b_adjStep_perm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc92borbitobstruction.lean)
-/
@[path]
private lemma gc92b_adjStep_perm_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {τ : Equiv.Perm ι}
  {K : Finset ι}
  {a b : W}
-- given
  (hτ : ∀ i, ends (τ i) = ends i) :
-- imply
  adjStep ends (K.image τ) a b ↔ adjStep ends K a b := by
-- proof
  apply StatMech.Walls.gc92b_adjStep_perm ends τ hτ K a b

/--
[gc92b_connK_perm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc92borbitobstruction.lean)
-/
@[path]
private lemma gc92b_connK_perm_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {τ : Equiv.Perm ι}
  {K : Finset ι}
  {a b : W}
-- given
  (hτ : ∀ i, ends (τ i) = ends i) :
-- imply
  connK ends (K.image τ) a b ↔ connK ends K a b := by
-- proof
  apply StatMech.Walls.gc92b_connK_perm ends τ hτ K a b

/--
[gc92b_image_sdiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc92borbitobstruction.lean)
-/
@[path]
private lemma gc92b_image_sdiff_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {τ : Equiv.Perm ι}
  {m K : Finset ι}
-- given
  (hm : m.image τ = m) :
-- imply
  (m \ K).image τ = m \ (K.image τ) := by
-- proof
  apply StatMech.Walls.gc92b_image_sdiff τ m K hm

/--
[gc92b_connK_complement_perm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc92borbitobstruction.lean)
-/
@[path]
private lemma gc92b_connK_complement_perm_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {τ : Equiv.Perm ι}
  {m K : Finset ι}
  {a b : W}
-- given
  (hτ : ∀ i, ends (τ i) = ends i)
  (hm : m.image τ = m) :
-- imply
  connK ends (m \ (K.image τ)) a b ↔ connK ends (m \ K) a b := by
-- proof
  apply StatMech.Walls.gc92b_connK_complement_perm ends τ hτ m K hm a b

/--
[gc92b_perm_mem_cogxgSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc92borbitobstruction.lean)
-/
@[path]
private lemma gc92b_perm_mem_cogxgSet_iff_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {τ : Equiv.Perm ι}
  {m : Finset ι}
  {o x g : W}
  {K₁ K₂ : Finset ι}
-- given
  (hτ : ∀ i, ends (τ i) = ends i)
  (hm : m.image τ = m) :
-- imply
  (K₁.image τ, K₂.image τ) ∈ gc91b_cogxgPairs ends m o x g ↔ (K₁, K₂) ∈ gc91b_cogxgPairs ends m o x g := by
-- proof
  apply StatMech.Walls.gc92b_perm_mem_cogxgSet_iff ends τ hτ m hm o x g K₁ K₂

/--
[gc92b_perm_mem_T3Set_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc92borbitobstruction.lean)
-/
@[path]
private lemma gc92b_perm_mem_T3Set_iff_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {τ : Equiv.Perm ι}
  {m : Finset ι}
  {o x y g : W}
  {J₁ J₂ : Finset ι}
-- given
  (hτ : ∀ i, ends (τ i) = ends i)
  (hm : m.image τ = m) :
-- imply
  (J₁.image τ, J₂.image τ) ∈ gc91b_T3Pairs ends m o x y g ↔ (J₁, J₂) ∈ gc91b_T3Pairs ends m o x y g := by
-- proof
  apply StatMech.Walls.gc92b_perm_mem_T3Set_iff ends τ hτ m hm o x y g J₁ J₂

/--
[gc92b_no_equivariant_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc92borbitobstruction.lean)
-/
@[path]
private lemma gc92b_no_equivariant_injection_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {τ : Equiv.Perm ι}
  {m : Finset ι}
  {o x y g : W}
  {s₁ s₂ : Finset ι × Finset ι}
  {f : Finset ι × Finset ι → Finset ι × Finset ι}
-- given
  (hs₁ : s₁ ∈ gc91b_cogxgPairs ends m o x g)
  (hs₂ : s₂ ∈ gc91b_cogxgPairs ends m o x g)
  (hswap : s₂ = gc92b_pairAction τ s₁)
  (hne : s₁ ≠ s₂)
  (hT3fixed : ∀ t ∈ gc91b_T3Pairs ends m o x y g, gc92b_pairAction τ t = t)
  (hmaps : ∀ s ∈ gc91b_cogxgPairs ends m o x g, f s ∈ gc91b_T3Pairs ends m o x y g)
  (hequiv : f (gc92b_pairAction τ s₁) = gc92b_pairAction τ (f s₁))
  (hinj : Set.InjOn f (gc91b_cogxgPairs ends m o x g)) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.gc92b_no_equivariant_injection ends τ m hs₁ hs₂ hswap hne hT3fixed f hmaps hequiv hinj

/--
[gc92b_wred_perm_fixes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc92borbitobstruction.lean)
-/
@[path]
private lemma gc92b_wred_perm_fixes_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  ∀ i : Fin 4, gc88b_wredEnds (Equiv.swap (1 : Fin 4) 2 i) = gc88b_wredEnds i := by
-- proof
  apply StatMech.Walls.gc92b_wred_perm_fixes

/--
[gc92b_wred_perm_fixes_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc92borbitobstruction.lean)
-/
@[path]
private lemma gc92b_wred_perm_fixes_univ_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  (univ : Finset (Fin 4)).image (Equiv.swap (1 : Fin 4) 2) = univ := by
-- proof
  apply StatMech.Walls.gc92b_wred_perm_fixes_univ

/--
[gc92b_wred_swap_cogxg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc92borbitobstruction.lean)
-/
@[path]
private lemma gc92b_wred_swap_cogxg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  ({1} : Finset (Fin 4)).image (Equiv.swap (1 : Fin 4) 2) = ({2} : Finset (Fin 4)) ∧ ({2} : Finset (Fin 4)).image (Equiv.swap (1 : Fin 4) 2) = ({1} : Finset (Fin 4)) ∧ (∅ : Finset (Fin 4)).image (Equiv.swap (1 : Fin 4) 2) = (∅ : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc92b_wred_swap_cogxg

/--
[gc92b_wred_swap_fixes_T3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc92borbitobstruction.lean)
-/
@[path]
private lemma gc92b_wred_swap_fixes_T3_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  gc92b_pairAction (Equiv.swap (1 : Fin 4) 2) ((∅ : Finset (Fin 4)), (∅ : Finset (Fin 4))) = ((∅ : Finset (Fin 4)), (∅ : Finset (Fin 4))) ∧ gc92b_pairAction (Equiv.swap (1 : Fin 4) 2) ((∅ : Finset (Fin 4)), ({1, 2} : Finset (Fin 4))) = ((∅ : Finset (Fin 4)), ({1, 2} : Finset (Fin 4))) := by
-- proof
  apply StatMech.Walls.gc92b_wred_swap_fixes_T3

/--
[gc92b_wred_mem_cogxg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc92borbitobstruction.lean)
-/
@[path]
private lemma gc92b_wred_mem_cogxg_one_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4))) ∈ gc91b_cogxgPairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 3 := by
-- proof
  apply StatMech.Walls.gc92b_wred_mem_cogxg_one

/--
[gc92b_wred_mem_cogxg_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc92borbitobstruction.lean)
-/
@[path]
private lemma gc92b_wred_mem_cogxg_two_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  (({2} : Finset (Fin 4)), (∅ : Finset (Fin 4))) ∈ gc91b_cogxgPairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 3 := by
-- proof
  apply StatMech.Walls.gc92b_wred_mem_cogxg_two

/--
[gc92b_wred_cogxg_swapped](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc92borbitobstruction.lean)
-/
@[path]
private lemma gc92b_wred_cogxg_swapped_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4))) ≠ (({2} : Finset (Fin 4)), (∅ : Finset (Fin 4))) ∧ gc92b_pairAction (Equiv.swap (1 : Fin 4) 2) (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4))) = (({2} : Finset (Fin 4)), (∅ : Finset (Fin 4))) := by
-- proof
  apply StatMech.Walls.gc92b_wred_cogxg_swapped

/--
[gc92b_wred_no_equivariant_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc92borbitobstruction.lean)
-/
@[path]
private lemma gc92b_wred_no_equivariant_injection_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {f : Finset (Fin 4) × Finset (Fin 4) → Finset (Fin 4) × Finset (Fin 4)}
-- given
  (hT3fixed : ∀ t ∈ gc91b_T3Pairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3, gc92b_pairAction (Equiv.swap (1 : Fin 4) 2) t = t)
  (hmaps : ∀ s ∈ gc91b_cogxgPairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 3, f s ∈ gc91b_T3Pairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3)
  (hequiv : f (gc92b_pairAction (Equiv.swap (1 : Fin 4) 2) (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4)))) = gc92b_pairAction (Equiv.swap (1 : Fin 4) 2) (f (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4)))))
  (hinj : Set.InjOn f (gc91b_cogxgPairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 3)) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.gc92b_wred_no_equivariant_injection hT3fixed f hmaps hequiv hinj

/--
[gc92b_orbit_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc92borbitobstruction.lean)
-/
@[path]
private lemma gc92b_orbit_status_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {τ : Equiv.Perm ι}
  {m : Finset ι}
  {o x y g : W}
  {s₁ s₂ : Finset ι × Finset ι}
-- given
  (hτ : ∀ i, ends (τ i) = ends i)
  (hm : m.image τ = m)
  (hs₁ : s₁ ∈ gc91b_cogxgPairs ends m o x g)
  (hs₂ : s₂ ∈ gc91b_cogxgPairs ends m o x g)
  (hswap : s₂ = gc92b_pairAction τ s₁)
  (hne : s₁ ≠ s₂)
  (hT3fixed : ∀ t ∈ gc91b_T3Pairs ends m o x y g, gc92b_pairAction τ t = t) :
-- imply
  (∀ K₁ K₂, (K₁.image τ, K₂.image τ) ∈ gc91b_cogxgPairs ends m o x g ↔ (K₁, K₂) ∈ gc91b_cogxgPairs ends m o x g) ∧ (∀ J₁ J₂, (J₁.image τ, J₂.image τ) ∈ gc91b_T3Pairs ends m o x y g ↔ (J₁, J₂) ∈ gc91b_T3Pairs ends m o x y g) ∧ (∀ f : Finset ι × Finset ι → Finset ι × Finset ι, (∀ s ∈ gc91b_cogxgPairs ends m o x g, f s ∈ gc91b_T3Pairs ends m o x y g) → f (gc92b_pairAction τ s₁) = gc92b_pairAction τ (f s₁) → Set.InjOn f (gc91b_cogxgPairs ends m o x g) → False) := by
-- proof
  apply StatMech.Walls.gc92b_orbit_status ends τ m hτ hm hs₁ hs₂ hswap hne hT3fixed

/--
[gc92b_machine_findings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc92borbitobstruction.lean)
-/
@[path]
private lemma gc92b_machine_findings_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  True := by
-- proof
  apply StatMech.Walls.gc92b_machine_findings


-- created on 2026-10-23
