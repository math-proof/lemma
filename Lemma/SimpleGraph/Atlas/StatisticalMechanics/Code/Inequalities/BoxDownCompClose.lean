import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Inequalities.BoxDownCompClose
open Finset MeasureTheory StatMech


/--
[bdc2_w_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_w_nonneg_eq :
-- imply
  ∀ x b, 0 ≤ bdc2_w x b := by
-- proof
  apply StatMech.bdc2_w_nonneg

/--
[bdc2_w_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_w_prob_eq :
-- imply
  ∀ x, bdc2_w x false + bdc2_w x true = 1 := by
-- proof
  apply StatMech.bdc2_w_prob

/--
[bdc2_w_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_w_symm_eq :
-- imply
  ∀ x, bdc2_w x false = bdc2_w x true := by
-- proof
  apply StatMech.bdc2_w_symm

/--
[bdc2_downComp_A](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_downComp_A_eq :
-- imply
  Down.compression 0 bdc2_A = bdc2_A := by
-- proof
  apply StatMech.bdc2_downComp_A

/--
[bdc2_downComp_B](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_downComp_B_eq :
-- imply
  Down.compression 0 bdc2_B = bdc2_A := by
-- proof
  apply StatMech.bdc2_downComp_B

/--
[bdc2_support_FF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_support_FF_eq :
-- imply
  cfgSupport bdc2_FF = (∅ : Finset (Fin 2)) := by
-- proof
  apply StatMech.bdc2_support_FF

/--
[bdc2_support_TF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_support_TF_eq :
-- imply
  cfgSupport bdc2_TF = ({0} : Finset (Fin 2)) := by
-- proof
  apply StatMech.bdc2_support_TF

/--
[bdc2_support_TT](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_support_TT_eq :
-- imply
  cfgSupport bdc2_TT = ({0, 1} : Finset (Fin 2)) := by
-- proof
  apply StatMech.bdc2_support_TT

/--
[bdc2_TF_ne_FF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_TF_ne_FF_eq :
-- imply
  bdc2_TF ≠ bdc2_FF := by
-- proof
  apply StatMech.bdc2_TF_ne_FF

/--
[bdc2_config_of_support_in_AB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_config_of_support_in_AB_eq
  {ω : ConfigSpace (Fin 2)}
-- given
  (h : cfgSupport ω = ∅ ∨ cfgSupport ω = {0}) :
-- imply
  ω = bdc2_FF ∨ ω = bdc2_TF := by
-- proof
  apply StatMech.bdc2_config_of_support_in_AB h

/--
[bdc2_support_mem_A_of_zero_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_support_mem_A_of_zero_false_eq
  {ω : ConfigSpace (Fin 2)}
-- given
  (h0 : ω 0 = false) :
-- imply
  cfgSupport ω ∈ bdc2_A := by
-- proof
  apply StatMech.bdc2_support_mem_A_of_zero_false h0

/--
[bdc2_support_mem_A_of_one_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_support_mem_A_of_one_false_eq
  {ω : ConfigSpace (Fin 2)}
-- given
  (h0 : ω 1 = false) :
-- imply
  cfgSupport ω ∈ bdc2_A := by
-- proof
  apply StatMech.bdc2_support_mem_A_of_one_false h0

/--
[bdc2_support_mem_B_of_one_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_support_mem_B_of_one_false_eq
  {ω : ConfigSpace (Fin 2)}
-- given
  (h0 : ω 1 = false) :
-- imply
  cfgSupport ω ∈ bdc2_B := by
-- proof
  apply StatMech.bdc2_support_mem_B_of_one_false h0

/--
[bdc2_support_mem_B_of_zero_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_support_mem_B_of_zero_true_eq
  {ω : ConfigSpace (Fin 2)}
-- given
  (h0 : ω 0 = true) :
-- imply
  cfgSupport ω ∈ bdc2_B := by
-- proof
  apply StatMech.bdc2_support_mem_B_of_zero_true h0

/--
[bdc2_FF_mem_box_AB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_FF_mem_box_AB_eq :
-- imply
  bdc2_FF ∈ disjointOccurrence (familyEvent bdc2_A) (familyEvent bdc2_B) := by
-- proof
  apply StatMech.bdc2_FF_mem_box_AB

/--
[bdc2_TF_mem_box_AB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_TF_mem_box_AB_eq :
-- imply
  bdc2_TF ∈ disjointOccurrence (familyEvent bdc2_A) (familyEvent bdc2_B) := by
-- proof
  apply StatMech.bdc2_TF_mem_box_AB

/--
[bdc2_FF_mem_box_compressed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_FF_mem_box_compressed_eq :
-- imply
  bdc2_FF ∈ disjointOccurrence (familyEvent bdc2_A) (familyEvent bdc2_A) := by
-- proof
  apply StatMech.bdc2_FF_mem_box_compressed

/--
[bdc2_TT_notMem_familyEvent_A](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_TT_notMem_familyEvent_A_eq :
-- imply
  bdc2_TT ∉ familyEvent bdc2_A := by
-- proof
  apply StatMech.bdc2_TT_notMem_familyEvent_A

/--
[bdc2_occursOn_forces_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_occursOn_forces_one_eq
  {K : Set (Fin 2)}
-- given
  (h : OccursOn (familyEvent bdc2_A) K bdc2_TF) :
-- imply
  (1 : Fin 2) ∈ K := by
-- proof
  apply StatMech.bdc2_occursOn_forces_one h

/--
[bdc2_TF_notMem_box_compressed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_TF_notMem_box_compressed_eq :
-- imply
  bdc2_TF ∉ disjointOccurrence (familyEvent bdc2_A) (familyEvent bdc2_A) := by
-- proof
  apply StatMech.bdc2_TF_notMem_box_compressed

/--
[bdc2_box_AB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_box_AB_eq :
-- imply
  disjointOccurrence (familyEvent bdc2_A) (familyEvent bdc2_B) = ({bdc2_FF, bdc2_TF} : Set (ConfigSpace (Fin 2))) := by
-- proof
  apply StatMech.bdc2_box_AB

/--
[bdc2_box_compressed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_box_compressed_eq :
-- imply
  disjointOccurrence (familyEvent bdc2_A) (familyEvent bdc2_A) = ({bdc2_FF} : Set (ConfigSpace (Fin 2))) := by
-- proof
  apply StatMech.bdc2_box_compressed

/--
[bdc2_pweight_TF_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_pweight_TF_pos_eq :
-- imply
  0 < pweight bdc2_w bdc2_TF := by
-- proof
  apply StatMech.bdc2_pweight_TF_pos

/--
[bdc2_wprob_strict_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_wprob_strict_mono_eq
  [Fintype E]
  [DecidableEq E]
  {φ : E → Bool → ℝ}
  {S T : Set (ConfigSpace E)}
  {x : ConfigSpace E}
-- given
  (hφ : ∀ x b, 0 ≤ φ x b)
  (hST : S ⊆ T)
  (hxT : x ∈ T)
  (hxS : x ∉ S)
  (hpx : 0 < pweight φ x) :
-- imply
  wprob φ S < wprob φ T := by
-- proof
  apply StatMech.bdc2_wprob_strict_mono hφ hST hxT hxS hpx

/--
[bdc2_wprob_compressed_lt_AB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_wprob_compressed_lt_AB_eq :
-- imply
  wprob bdc2_w (disjointOccurrence (familyEvent bdc2_A) (familyEvent bdc2_A)) < wprob bdc2_w (disjointOccurrence (familyEvent bdc2_A) (familyEvent bdc2_B)) := by
-- proof
  apply StatMech.bdc2_wprob_compressed_lt_AB

/--
[bdc2_boxDownCompMono_fin2_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean)
-/
@[path]
private lemma bdc2_boxDownCompMono_fin2_false_eq :
-- imply
  ¬ rit_BoxDownCompMono (Fin 2) := by
-- proof
  apply StatMech.bdc2_boxDownCompMono_fin2_false


-- created on 2026-10-23
