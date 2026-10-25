import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc6relabelinvariance.Part2
open Finset StatMech StatMech.Walls


/--
[rc6_preimage_inter_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6relabelinvariance.lean)
-/
@[path]
private lemma rc6_preimage_inter_reflect_eq
  {e : E ≃ F}
  {A B : Set (ConfigSpace E)} :
-- imply
  (cfgEquiv e) ⁻¹' (A ∩ rmr_reflect B) = (cfgEquiv e ⁻¹' A) ∩ rmr_reflect (cfgEquiv e ⁻¹' B) := by
-- proof
  apply StatMech.Walls.rc6_preimage_inter_reflect e A B

/--
[rc6_deficit_cfgEquiv_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6relabelinvariance.lean)
-/
@[path]
private lemma rc6_deficit_cfgEquiv_invariant_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype F]
  [DecidableEq F]
  {e : E ≃ F}
  {A B : Set (ConfigSpace E)} :
-- imply
  rc6_deficit A B = rc6_deficit (cfgEquiv e ⁻¹' A) (cfgEquiv e ⁻¹' B) := by
-- proof
  apply StatMech.Walls.rc6_deficit_cfgEquiv_invariant e A B

/--
[rc6_deficit_relabel_to_fin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6relabelinvariance.lean)
-/
@[path]
private lemma rc6_deficit_relabel_to_fin_eq
  [Fintype β]
  [DecidableEq β]
  {A B : Set (ConfigSpace β)} :
-- imply
  ∃ (e : β ≃ Fin (Fintype.card β)), rc6_deficit A B = rc6_deficit (cfgEquiv e ⁻¹' A) (cfgEquiv e ⁻¹' B) := by
-- proof
  apply StatMech.Walls.rc6_deficit_relabel_to_fin A B

/--
[rc6_deficitNonpos_of_fin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6relabelinvariance.lean)
-/
@[path]
private lemma rc6_deficitNonpos_of_fin_eq
  [Fintype β]
  [DecidableEq β]
  {A B : Set (ConfigSpace β)}
-- given
  (h : rc6_DeficitNonpos) :
-- imply
  rc6_deficit A B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc6_deficitNonpos_of_fin h A B

/--
[rc6_deficitNonposAllFinite_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6relabelinvariance.lean)
-/
@[path]
private lemma rc6_deficitNonposAllFinite_iff_eq :
-- imply
  rc6_DeficitNonposAllFinite ↔ rc6_DeficitNonpos := by
-- proof
  apply StatMech.Walls.rc6_deficitNonposAllFinite_iff

/--
[rc6_reimerCardFormAll_iff_deficitNonposAllFinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6relabelinvariance.lean)
-/
@[path]
private lemma rc6_reimerCardFormAll_iff_deficitNonposAllFinite_eq :
-- imply
  ReimerCardFormAll ↔ rc6_DeficitNonposAllFinite := by
-- proof
  apply StatMech.Walls.rc6_reimerCardFormAll_iff_deficitNonposAllFinite

/--
[rc6_reimerCardForm_of_reimerCardFormAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6relabelinvariance.lean)
-/
@[path]
private lemma rc6_reimerCardForm_of_reimerCardFormAll_eq
  [Fintype β]
  [DecidableEq β]
  {A B : Set (ConfigSpace β)}
-- given
  (hcard : ReimerCardFormAll) :
-- imply
  StatMech.poc_ReimerCardForm A B := by
-- proof
  apply StatMech.Walls.rc6_reimerCardForm_of_reimerCardFormAll hcard A B

/--
[rc6_relabel_invariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6relabelinvariance.lean)
-/
@[path]
private lemma rc6_relabel_invariance_eq :
-- imply
  (∀ {E F : Type} [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F] (e : E ≃ F) (A B : Set (ConfigSpace E)), rc6_deficit A B = rc6_deficit (cfgEquiv e ⁻¹' A) (cfgEquiv e ⁻¹' B)) ∧ (rc6_DeficitNonposAllFinite ↔ rc6_DeficitNonpos) ∧ (ReimerCardFormAll ↔ rc6_DeficitNonposAllFinite) := by
-- proof
  apply StatMech.Walls.rc6_relabel_invariance


-- created on 2026-10-23
