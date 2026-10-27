import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc19doublecover.Part4
open Finset StatMech StatMech.Walls


/--
[rc19_mem_cylBoxSupp_iff_minimal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc19doublecover.lean)
-/
@[path]
private lemma rc19_mem_cylBoxSupp_iff_minimal_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S : Finset α} :
-- imply
  S ∈ rc18_cylBoxSupp A B ↔ ∃ K L : Finset α, Disjoint K L ∧ Minimal (fun T => cylinder T (supportCfg S) ⊆ A) K ∧ Minimal (fun T => cylinder T (supportCfg S) ⊆ B) L := by
-- proof
  apply StatMech.Walls.rc19_mem_cylBoxSupp_iff_minimal A B S

/--
[rc19_cylBoxSupp_iff_doubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc19doublecover.lean)
-/
@[path]
private lemma rc19_cylBoxSupp_iff_doubled_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S : Finset α} :
-- imply
  S ∈ rc18_cylBoxSupp A B ↔ (rc19_cylDoubledBox A B S).Nonempty := by
-- proof
  apply StatMech.Walls.rc19_cylBoxSupp_iff_doubled A B S

/--
[rc19_dbl_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc19doublecover.lean)
-/
@[path]
private lemma rc19_dbl_inj_eq
  [Fintype α]
  [DecidableEq α]
  {K L K' L' : Finset α}
-- given
  (h : dbl K L = dbl K' L') :
-- imply
  K = K' ∧ L = L' := by
-- proof
  apply StatMech.Walls.rc19_dbl_inj h

/--
[rc19_mem_reflInter_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc19doublecover.lean)
-/
@[path]
private lemma rc19_mem_reflInter_iff_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S : Finset α} :
-- imply
  S ∈ rc10_reflInter (eventFamily A) (eventFamily B) ↔ supportCfg S ∈ A ∧ supportCfg (Sᶜ) ∈ B := by
-- proof
  apply StatMech.Walls.rc19_mem_reflInter_iff A B S

/--
[rc19_reflInter_diag_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc19doublecover.lean)
-/
@[path]
private lemma rc19_reflInter_diag_injOn_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  Set.InjOn (fun S : Finset α => dbl S Sᶜ) (rc10_reflInter (eventFamily A) (eventFamily B) : Set (Finset α)) := by
-- proof
  apply StatMech.Walls.rc19_reflInter_diag_injOn A B

/--
[rc19_cylBoxReflInter_of_doubledReflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc19doublecover.lean)
-/
@[path]
private lemma rc19_cylBoxReflInter_of_doubledReflection_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (h : rc19_DoubledReflection A B) :
-- imply
  #(rc18_cylBoxSupp A B) ≤ #(rc10_reflInter (eventFamily A) (eventFamily B)) := by
-- proof
  apply StatMech.Walls.rc19_cylBoxReflInter_of_doubledReflection h

/--
[rc19_doubledReflection_of_cylBoxReflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc19doublecover.lean)
-/
@[path]
private lemma rc19_doubledReflection_of_cylBoxReflInter_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (h : #(rc18_cylBoxSupp A B) ≤ #(rc10_reflInter (eventFamily A) (eventFamily B))) :
-- imply
  rc19_DoubledReflection A B := by
-- proof
  apply StatMech.Walls.rc19_doubledReflection_of_cylBoxReflInter h

/--
[rc19_doubledReflection_iff_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc19doublecover.lean)
-/
@[path]
private lemma rc19_doubledReflection_iff_card_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  rc19_DoubledReflection A B ↔ #(rc18_cylBoxSupp A B) ≤ #(rc10_reflInter (eventFamily A) (eventFamily B)) := by
-- proof
  apply StatMech.Walls.rc19_doubledReflection_iff_card A B

/--
[rc19_doubledReflectionAll_iff_cylBoxReflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc19doublecover.lean)
-/
@[path]
private lemma rc19_doubledReflectionAll_iff_cylBoxReflInter_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc19_DoubledReflectionAll ↔ rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc19_doubledReflectionAll_iff_cylBoxReflInter

/--
[rc19_reimerWprobCore_of_doubledReflectionAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc19doublecover.lean)
-/
@[path]
private lemma rc19_reimerWprobCore_of_doubledReflectionAll_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc19_DoubledReflectionAll) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc19_reimerWprobCore_of_doubledReflectionAll h


-- created on 2026-10-23
