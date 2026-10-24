import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc16sliceunion
open Finset StatMech StatMech.Walls


/--
[rc16_boxE_left_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc16sliceunion.lean)
-/
@[path]
private lemma rc16_boxE_left_subset_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 𝒜' ℬ : Finset (Finset α)}
-- given
  (h : 𝒜 ⊆ 𝒜') :
-- imply
  rc14_boxE E 𝒜 ℬ ⊆ rc14_boxE E 𝒜' ℬ := by
-- proof
  apply StatMech.Walls.rc16_boxE_left_subset h

/--
[rc16_boxE_right_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc16sliceunion.lean)
-/
@[path]
private lemma rc16_boxE_right_subset_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 ℬ ℬ' : Finset (Finset α)}
-- given
  (h : ℬ ⊆ ℬ') :
-- imply
  rc14_boxE E 𝒜 ℬ ⊆ rc14_boxE E 𝒜 ℬ' := by
-- proof
  apply StatMech.Walls.rc16_boxE_right_subset h

/--
[rc16_boxE_nonMem_subset_mem_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc16sliceunion.lean)
-/
@[path]
private lemma rc16_boxE_nonMem_subset_mem_left_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 ℬ : Finset (Finset α)}
  {a : α}
-- given
  (h𝒜 : rc15_UpperOn E 𝒜)
  (haE : a ∈ E) :
-- imply
  rc14_boxE (E.erase a) (𝒜.nonMemberSubfamily a) ℬ ⊆ rc14_boxE (E.erase a) (𝒜.memberSubfamily a) ℬ := by
-- proof
  apply StatMech.Walls.rc16_boxE_nonMem_subset_mem_left h𝒜 a haE

/--
[rc16_boxE_nonMem_subset_mem_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc16sliceunion.lean)
-/
@[path]
private lemma rc16_boxE_nonMem_subset_mem_right_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 ℬ : Finset (Finset α)}
  {a : α}
-- given
  (hℬ : rc15_UpperOn E ℬ)
  (haE : a ∈ E) :
-- imply
  rc14_boxE (E.erase a) 𝒜 (ℬ.nonMemberSubfamily a) ⊆ rc14_boxE (E.erase a) 𝒜 (ℬ.memberSubfamily a) := by
-- proof
  apply StatMech.Walls.rc16_boxE_nonMem_subset_mem_right hℬ a haE

/--
[rc16_boxE_base_subset_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc16sliceunion.lean)
-/
@[path]
private lemma rc16_boxE_base_subset_inter_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 ℬ : Finset (Finset α)}
  {a : α}
-- given
  (h𝒜 : rc15_UpperOn E 𝒜)
  (hℬ : rc15_UpperOn E ℬ)
  (haE : a ∈ E) :
-- imply
  rc14_boxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a) ⊆ rc14_boxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a) ∩ rc14_boxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a) := by
-- proof
  apply StatMech.Walls.rc16_boxE_base_subset_inter h𝒜 hℬ a haE

/--
[rc16_bkrground_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc16sliceunion.lean)
-/
@[path]
private lemma rc16_bkrground_step_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {a : α}
-- given
  (haE : a ∈ E)
  (hIH : rc15_BKRground (E.erase a)) :
-- imply
  rc15_BKRground E := by
-- proof
  apply StatMech.Walls.rc16_bkrground_step haE hIH

/--
[rc16_bkrground](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc16sliceunion.lean)
-/
@[path]
private lemma rc16_bkrground_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∀ E : Finset α, rc15_BKRground E := by
-- proof
  apply StatMech.Walls.rc16_bkrground

/--
[rc16_bkrSetFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc16sliceunion.lean)
-/
@[path]
private lemma rc16_bkrSetFamily_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc10_BKRSetFamily := by
-- proof
  apply StatMech.Walls.rc16_bkrSetFamily

/--
[rc16_bkrInjectionAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc16sliceunion.lean)
-/
@[path]
private lemma rc16_bkrInjectionAll_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc11_BKRInjectionAll := by
-- proof
  apply StatMech.Walls.rc16_bkrInjectionAll

/--
[rc16_deficitBridgeIncInc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc16sliceunion.lean)
-/
@[path]
private lemma rc16_deficitBridgeIncInc_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc10_DeficitBridgeIncInc := by
-- proof
  apply StatMech.Walls.rc16_deficitBridgeIncInc


-- created on 2026-10-23
