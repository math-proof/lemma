import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyInjClose.Part2
open Finset StatMech


/--
[rbi_cfg_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyInjClose.lean)
-/
@[path]
private lemma rbi_cfg_zero_eq
  {a b : Bool} :
-- imply
  rbi_cfg a b 0 = a := by
-- proof
  apply StatMech.rbi_cfg_zero a b

/--
[rbi_cfg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyInjClose.lean)
-/
@[path]
private lemma rbi_cfg_one_eq
  {a b : Bool} :
-- imply
  rbi_cfg a b 1 = b := by
-- proof
  apply StatMech.rbi_cfg_one a b

/--
[rbi_fin2_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyInjClose.lean)
-/
@[path]
private lemma rbi_fin2_cases_eq
  {e : Fin 2} :
-- imply
  e = 0 ∨ e = 1 := by
-- proof
  apply StatMech.rbi_fin2_cases e

/--
[rbi_FF_in_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyInjClose.lean)
-/
@[path]
private lemma rbi_FF_in_box_eq :
-- imply
  rbi_cfg false false ∈ disjointOccurrence rbi_A rbi_B := by
-- proof
  apply StatMech.rbi_FF_in_box

/--
[rbi_FT_in_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyInjClose.lean)
-/
@[path]
private lemma rbi_FT_in_box_eq :
-- imply
  rbi_cfg false true ∈ disjointOccurrence rbi_A rbi_B := by
-- proof
  apply StatMech.rbi_FT_in_box

/--
[rbi_force_FF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyInjClose.lean)
-/
@[path]
private lemma rbi_force_FF_eq
  {K : Fin 2 → Bool}
-- given
  (hA : OccursOn rbi_A {a : Fin 2 | K a = true} (rbi_cfg false false))
  (hB : OccursOn rbi_B {a : Fin 2 | K a = false} (rbi_cfg false false)) :
-- imply
  K 0 = false ∧ K 1 = true := by
-- proof
  apply StatMech.rbi_force_FF K hA hB

/--
[rbi_force_FT](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyInjClose.lean)
-/
@[path]
private lemma rbi_force_FT_eq
  {K : Fin 2 → Bool}
-- given
  (hA : OccursOn rbi_A {a : Fin 2 | K a = true} (rbi_cfg false true))
  (hB : OccursOn rbi_B {a : Fin 2 | K a = false} (rbi_cfg false true)) :
-- imply
  K 0 = true ∧ K 1 = false := by
-- proof
  apply StatMech.rbi_force_FT K hA hB

/--
[rbi_collision_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyInjClose.lean)
-/
@[path]
private lemma rbi_collision_fst_eq
  {w1 w2 : Fin 2 → Bool}
-- given
  (a0 : w1 0 = false)
  (a1 : w1 1 = true)
  (b0 : w2 0 = true)
  (b1 : w2 1 = false) :
-- imply
  bglue w1 (rbi_cfg false false) (rbi_cfg false true) = bglue w2 (rbi_cfg false true) (rbi_cfg false false) := by
-- proof
  apply StatMech.rbi_collision_fst w1 w2 a0 a1 b0 b1

/--
[rbi_collision_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyInjClose.lean)
-/
@[path]
private lemma rbi_collision_snd_eq
  {w1 w2 : Fin 2 → Bool}
-- given
  (a0 : w1 0 = false)
  (a1 : w1 1 = true)
  (b0 : w2 0 = true)
  (b1 : w2 1 = false) :
-- imply
  bglue w1 (rbi_cfg false true) (rbi_cfg false false) = bglue w2 (rbi_cfg false false) (rbi_cfg false true) := by
-- proof
  apply StatMech.rbi_collision_snd w1 w2 a0 a1 b0 b1

/--
[rbi_pairs_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyInjClose.lean)
-/
@[path]
private lemma rbi_pairs_ne_eq :
-- imply
  ((rbi_cfg false false, rbi_cfg false true) : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) ≠ (rbi_cfg false true, rbi_cfg false false) := by
-- proof
  apply StatMech.rbi_pairs_ne

/--
[rbi_doubleCover_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyInjClose.lean)
-/
@[path]
private lemma rbi_doubleCover_false_eq :
-- imply
  ¬ rdc_DoubleCover rbi_A rbi_B := by
-- proof
  apply StatMech.rbi_doubleCover_false

/--
[rbi_doubleCoverAll_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyInjClose.lean)
-/
@[path]
private lemma rbi_doubleCoverAll_false_eq :
-- imply
  ¬ rdc_DoubleCoverAll := by
-- proof
  apply StatMech.rbi_doubleCoverAll_false

/--
[rbi_box_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyInjClose.lean)
-/
@[path]
private lemma rbi_box_eq_eq :
-- imply
  disjointOccurrence rbi_A rbi_B = {rbi_cfg false false, rbi_cfg false true} := by
-- proof
  apply StatMech.rbi_box_eq


-- created on 2026-10-23
