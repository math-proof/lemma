import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc82fixedordercompress
open Finset StatMech StatMech.Walls


/--
[rc82_downMap_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc82fixedordercompress.lean)
-/
@[path]
private lemma rc82_downMap_injOn_eq
  [Fintype ι]
  [DecidableEq ι]
  {i : ι}
  {A : Finset (ConfigSpace ι)} :
-- imply
  Set.InjOn (rc82_downMap i A) A := by
-- proof
  apply StatMech.Walls.rc82_downMap_injOn i A

/--
[rc82_upMap_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc82fixedordercompress.lean)
-/
@[path]
private lemma rc82_upMap_injOn_eq
  [Fintype ι]
  [DecidableEq ι]
  {i : ι}
  {B : Finset (ConfigSpace ι)} :
-- imply
  Set.InjOn (rc82_upMap i B) B := by
-- proof
  apply StatMech.Walls.rc82_upMap_injOn i B

/--
[rc82_downCompressA_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc82fixedordercompress.lean)
-/
@[path]
private lemma rc82_downCompressA_card_eq
  [Fintype ι]
  [DecidableEq ι]
  {i : ι}
  {A : Finset (ConfigSpace ι)} :
-- imply
  (rc82_downCompressA i A).card = A.card := by
-- proof
  apply StatMech.Walls.rc82_downCompressA_card i A

/--
[rc82_upCompressB_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc82fixedordercompress.lean)
-/
@[path]
private lemma rc82_upCompressB_card_eq
  [Fintype ι]
  [DecidableEq ι]
  {i : ι}
  {B : Finset (ConfigSpace ι)} :
-- imply
  (rc82_upCompressB i B).card = B.card := by
-- proof
  apply StatMech.Walls.rc82_upCompressB_card i B

/--
[rc82_occ_lower_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc82fixedordercompress.lean)
-/
@[path]
private lemma rc82_occ_lower_iff_eq
  [Fintype ι]
  [DecidableEq ι]
  {A : Finset (ConfigSpace ι)}
  {K : Finset ι}
  {w : ConfigSpace ι}
-- given
  (hA : rc80_IsLower A) :
-- imply
  rc80_occ A K w = true ↔ rc80_maxext K w ∈ A := by
-- proof
  apply StatMech.Walls.rc82_occ_lower_iff hA K w

/--
[rc82_occ_upper_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc82fixedordercompress.lean)
-/
@[path]
private lemma rc82_occ_upper_iff_eq
  [Fintype ι]
  [DecidableEq ι]
  {B : Finset (ConfigSpace ι)}
  {L : Finset ι}
  {w : ConfigSpace ι}
-- given
  (hB : rc80_IsUpper B) :
-- imply
  rc80_occ B L w = true ↔ rc80_minext L w ∈ B := by
-- proof
  apply StatMech.Walls.rc82_occ_upper_iff hB L w

/--
[rc82_disjOccG_eq_inter_of_lower_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc82fixedordercompress.lean)
-/
@[path]
private lemma rc82_disjOccG_eq_inter_of_lower_upper_eq
  [Fintype ι]
  [DecidableEq ι]
  {A B : Finset (ConfigSpace ι)}
-- given
  (hA : rc80_IsLower A)
  (hB : rc80_IsUpper B) :
-- imply
  rc80_disjOccG A B = A ∩ B := by
-- proof
  apply StatMech.Walls.rc82_disjOccG_eq_inter_of_lower_upper hA hB

/--
[rc82_wall_lower_upper_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc82fixedordercompress.lean)
-/
@[path]
private lemma rc82_wall_lower_upper_iff_eq
  [Fintype ι]
  [DecidableEq ι]
  {A B : Finset (ConfigSpace ι)}
-- given
  (hA : rc80_IsLower A)
  (hB : rc80_IsUpper B) :
-- imply
  (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card ↔ (A ∩ B).card ≤ (rc80_reflInterG A B).card := by
-- proof
  apply StatMech.Walls.rc82_wall_lower_upper_iff hA hB

/--
[rc82_wall_holds_everywhere_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc82fixedordercompress.lean)
-/
@[path]
private lemma rc82_wall_holds_everywhere_fin2_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ∀ A B : Finset (ConfigSpace (Fin 2)), (rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card := by
-- proof
  apply StatMech.Walls.rc82_wall_holds_everywhere_fin2

/--
[rc82_reflInter_orig_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc82fixedordercompress.lean)
-/
@[path]
private lemma rc82_reflInter_orig_zero_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (rc80_reflInterG rc82_wA rc82_wA).card = 0 := by
-- proof
  apply StatMech.Walls.rc82_reflInter_orig_zero

/--
[rc82_downClosure_wA_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc82fixedordercompress.lean)
-/
@[path]
private lemma rc82_downClosure_wA_univ_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  rc81_downClosure rc82_wA = (Finset.univ : Finset (ConfigSpace (Fin 2))) := by
-- proof
  apply StatMech.Walls.rc82_downClosure_wA_univ

/--
[rc82_reflInter_shifted_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc82fixedordercompress.lean)
-/
@[path]
private lemma rc82_reflInter_shifted_one_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (rc80_reflInterG (rc81_downClosure rc82_wA) rc82_wA).card = 1 := by
-- proof
  apply StatMech.Walls.rc82_reflInter_shifted_one

/--
[rc82_downup_shift_refutes_wall_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc82fixedordercompress.lean)
-/
@[path]
private lemma rc82_downup_shift_refutes_wall_witness_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (rc80_reflInterG rc82_wA rc82_wA).card < (rc80_reflInterG (rc81_downClosure rc82_wA) rc82_wA).card := by
-- proof
  apply StatMech.Walls.rc82_downup_shift_refutes_wall_witness

/--
[rc82_lowerWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc82fixedordercompress.lean)
-/
@[path]
private lemma rc82_lowerWitness_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  rc80_IsLower ({rc81_botF} : Finset (ConfigSpace (Fin 2))) := by
-- proof
  apply StatMech.Walls.rc82_lowerWitness

/--
[rc82_upperWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc82fixedordercompress.lean)
-/
@[path]
private lemma rc82_upperWitness_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  rc80_IsUpper ({rc82_topF} : Finset (ConfigSpace (Fin 2))) := by
-- proof
  apply StatMech.Walls.rc82_upperWitness

/--
[rc82_dualWitness_reduces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc82fixedordercompress.lean)
-/
@[path]
private lemma rc82_dualWitness_reduces_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  rc80_disjOccG ({rc81_botF} : Finset (ConfigSpace (Fin 2))) {rc82_topF} = ({rc81_botF} : Finset (ConfigSpace (Fin 2))) ∩ {rc82_topF} := by
-- proof
  apply StatMech.Walls.rc82_dualWitness_reduces

/--
[rc82_reimerWprobCore_of_boxUnionBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc82fixedordercompress.lean)
-/
@[path]
private lemma rc82_reimerWprobCore_of_boxUnionBound_eq
  [Fintype ι]
  [DecidableEq ι]
-- given
  (h : rc60_BoxUnionBound) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc82_reimerWprobCore_of_boxUnionBound h

/--
[rc82_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc82fixedordercompress.lean)
-/
@[path]
private lemma rc82_status_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (A : Finset (ConfigSpace ι)), (rc82_downCompressA i A).card = A.card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (B : Finset (ConfigSpace ι)), (rc82_upCompressB i B).card = B.card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), rc80_IsLower A → rc80_IsUpper B → rc80_disjOccG A B = A ∩ B) ∧ (∀ A B : Finset (ConfigSpace (Fin 2)), (rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card) ∧ ((rc80_reflInterG rc82_wA rc82_wA).card < (rc80_reflInterG (rc81_downClosure rc82_wA) rc82_wA).card) ∧ (rc60_BoxUnionBound → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc82_status


-- created on 2026-10-23
