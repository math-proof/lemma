import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerPairWitnessClose.Part4
open Finset MeasureTheory StatMech


/--
[bfly2_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerPairWitnessClose.lean)
-/
@[path]
private lemma bfly2_fst_eq
  [Fintype α]
  [DecidableEq α]
  {wit : ConfigSpace α × ConfigSpace α → (α → Bool)}
  {p : ConfigSpace α × ConfigSpace α} :
-- imply
  (bfly2 wit p).1 = bglue (wit p) p.1 p.2 := by
-- proof
  apply StatMech.bfly2_fst wit p

/--
[bfly2_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerPairWitnessClose.lean)
-/
@[path]
private lemma bfly2_snd_eq
  [Fintype α]
  [DecidableEq α]
  {wit : ConfigSpace α × ConfigSpace α → (α → Bool)}
  {p : ConfigSpace α × ConfigSpace α} :
-- imply
  (bfly2 wit p).2 = bglue (wit p) p.2 p.1 := by
-- proof
  apply StatMech.bfly2_snd wit p

/--
[rpw_p1_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerPairWitnessClose.lean)
-/
@[path]
private lemma rpw_p1_mem_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rpw_p1 ∈ {p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) | p.1 ∈ disjointOccurrence rbi_A rbi_B} := by
-- proof
  apply StatMech.rpw_p1_mem

/--
[rpw_p2_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerPairWitnessClose.lean)
-/
@[path]
private lemma rpw_p2_mem_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rpw_p2 ∈ {p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) | p.1 ∈ disjointOccurrence rbi_A rbi_B} := by
-- proof
  apply StatMech.rpw_p2_mem

/--
[rpw_p1_ne_p2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerPairWitnessClose.lean)
-/
@[path]
private lemma rpw_p1_ne_p2_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rpw_p1 ≠ rpw_p2 := by
-- proof
  apply StatMech.rpw_p1_ne_p2

/--
[rpw_pairDoubleCover_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerPairWitnessClose.lean)
-/
@[path]
private lemma rpw_pairDoubleCover_false_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ rpw_PairDoubleCover rbi_A rbi_B := by
-- proof
  apply StatMech.rpw_pairDoubleCover_false

/--
[rpw_pairDoubleCoverAll_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerPairWitnessClose.lean)
-/
@[path]
private lemma rpw_pairDoubleCoverAll_false_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ (∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), rpw_PairDoubleCover A B) := by
-- proof
  apply StatMech.rpw_pairDoubleCoverAll_false

/--
[rpw_reimer_wprob_of_weightInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerPairWitnessClose.lean)
-/
@[path]
private lemma rpw_reimer_wprob_of_weightInjection_eq
  [Fintype α]
  [DecidableEq α]
  {φ : α → Bool → ℝ}
  {A B : Set (ConfigSpace α)}
-- given
  (hφ0 : ∀ x b, 0 ≤ φ x b)
  (hφ1 : ∀ x, φ x false + φ x true = 1)
  (hWI : rpw_WeightInjection A B) :
-- imply
  wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
-- proof
  apply StatMech.rpw_reimer_wprob_of_weightInjection φ hφ0 hφ1 hWI

/--
[rpw_weightInjection_of_doubleCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerPairWitnessClose.lean)
-/
@[path]
private lemma rpw_weightInjection_of_doubleCover_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hDC : rdc_DoubleCover A B) :
-- imply
  rpw_WeightInjection A B := by
-- proof
  apply StatMech.rpw_weightInjection_of_doubleCover hDC

/--
[rpw_weightInjection_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerPairWitnessClose.lean)
-/
@[path]
private lemma rpw_weightInjection_of_disjoint_support_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S T : Finset α}
-- given
  (hA : DependsOn A (↑S))
  (hB : DependsOn B (↑T))
  (hST : Disjoint S T) :
-- imply
  rpw_WeightInjection A B := by
-- proof
  apply StatMech.rpw_weightInjection_of_disjoint_support hA hB hST

/--
[rpw_weightInjection_of_box_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerPairWitnessClose.lean)
-/
@[path]
private lemma rpw_weightInjection_of_box_empty_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hbox : disjointOccurrence A B = ∅) :
-- imply
  rpw_WeightInjection A B := by
-- proof
  apply StatMech.rpw_weightInjection_of_box_empty hbox

/--
[rpw_reimer_wprob_core_of_weightInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerPairWitnessClose.lean)
-/
@[path]
private lemma rpw_reimer_wprob_core_of_weightInjection_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rpw_WeightInjectionAll) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.rpw_reimer_wprob_core_of_weightInjection h

/--
[rpw_reimer_inequality_of_weightInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerPairWitnessClose.lean)
-/
@[path]
private lemma rpw_reimer_inequality_of_weightInjection_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (h : rpw_WeightInjectionAll)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.rpw_reimer_inequality_of_weightInjection h hp A B


-- created on 2026-10-23
