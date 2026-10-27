import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubleCoverClose.Part4
open Finset MeasureTheory StatMech


/--
[bglue_agreeOn_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubleCoverClose.lean)
-/
@[path]
private lemma bglue_agreeOn_true_eq
  [Fintype α]
  [DecidableEq α]
  {K : α → Bool}
  {ω τ : ConfigSpace α} :
-- imply
  agreeOn {a | K a = true} ω (bglue K ω τ) := by
-- proof
  apply StatMech.bglue_agreeOn_true K ω τ

/--
[bglue_agreeOn_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubleCoverClose.lean)
-/
@[path]
private lemma bglue_agreeOn_false_eq
  [Fintype α]
  [DecidableEq α]
  {K : α → Bool}
  {ω τ : ConfigSpace α} :
-- imply
  agreeOn {a | K a = false} ω (bglue K τ ω) := by
-- proof
  apply StatMech.bglue_agreeOn_false K ω τ

/--
[bglue_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubleCoverClose.lean)
-/
@[path]
private lemma bglue_weight_eq
  [Fintype α]
  [DecidableEq α]
  {φ : α → Bool → ℝ}
  {K : α → Bool}
  {ω τ : ConfigSpace α} :
-- imply
  pweight φ (bglue K ω τ) * pweight φ (bglue K τ ω) = pweight φ ω * pweight φ τ := by
-- proof
  apply StatMech.bglue_weight φ K ω τ

/--
[bglue_bglue_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubleCoverClose.lean)
-/
@[path]
private lemma bglue_bglue_left_eq
  [Fintype α]
  [DecidableEq α]
  {K : α → Bool}
  {ω τ : ConfigSpace α} :
-- imply
  bglue K (bglue K ω τ) (bglue K τ ω) = ω := by
-- proof
  apply StatMech.bglue_bglue_left K ω τ

/--
[bglue_bglue_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubleCoverClose.lean)
-/
@[path]
private lemma bglue_bglue_right_eq
  [Fintype α]
  [DecidableEq α]
  {K : α → Bool}
  {ω τ : ConfigSpace α} :
-- imply
  bglue K (bglue K τ ω) (bglue K ω τ) = τ := by
-- proof
  apply StatMech.bglue_bglue_right K ω τ

/--
[bfly_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubleCoverClose.lean)
-/
@[path]
private lemma bfly_fst_eq
  [Fintype α]
  [DecidableEq α]
  {wit : ConfigSpace α → (α → Bool)}
  {p : ConfigSpace α × ConfigSpace α} :
-- imply
  (bfly wit p).1 = bglue (wit p.1) p.1 p.2 := by
-- proof
  apply StatMech.bfly_fst wit p

/--
[bfly_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubleCoverClose.lean)
-/
@[path]
private lemma bfly_snd_eq
  [Fintype α]
  [DecidableEq α]
  {wit : ConfigSpace α → (α → Bool)}
  {p : ConfigSpace α × ConfigSpace α} :
-- imply
  (bfly wit p).2 = bglue (wit p.1) p.2 p.1 := by
-- proof
  apply StatMech.bfly_snd wit p

/--
[rdc_reimer_wprob_of_doubleCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubleCoverClose.lean)
-/
@[path]
private lemma rdc_reimer_wprob_of_doubleCover_eq
  [Fintype α]
  [DecidableEq α]
  {φ : α → Bool → ℝ}
  {A B : Set (ConfigSpace α)}
-- given
  (hφ0 : ∀ x b, 0 ≤ φ x b)
  (hφ1 : ∀ x, φ x false + φ x true = 1)
  (hDC : rdc_DoubleCover A B) :
-- imply
  wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
-- proof
  apply StatMech.rdc_reimer_wprob_of_doubleCover φ hφ0 hφ1 hDC

/--
[rdc_bfly_const_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubleCoverClose.lean)
-/
@[path]
private lemma rdc_bfly_const_injective_eq
  [Fintype α]
  [DecidableEq α]
  {K₀ : α → Bool} :
-- imply
  Function.Injective (bfly (fun _ => K₀) : ConfigSpace α × ConfigSpace α → _) := by
-- proof
  apply StatMech.rdc_bfly_const_injective K₀

/--
[rdc_doubleCover_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubleCoverClose.lean)
-/
@[path]
private lemma rdc_doubleCover_of_disjoint_support_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S T : Finset α}
-- given
  (hA : DependsOn A (↑S))
  (hB : DependsOn B (↑T))
  (hST : Disjoint S T) :
-- imply
  rdc_DoubleCover A B := by
-- proof
  apply StatMech.rdc_doubleCover_of_disjoint_support hA hB hST

/--
[rdc_doubleCover_of_box_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubleCoverClose.lean)
-/
@[path]
private lemma rdc_doubleCover_of_box_empty_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hbox : disjointOccurrence A B = ∅) :
-- imply
  rdc_DoubleCover A B := by
-- proof
  apply StatMech.rdc_doubleCover_of_box_empty hbox

/--
[rdc_doubleCover_empty_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubleCoverClose.lean)
-/
@[path]
private lemma rdc_doubleCover_empty_left_eq
  [Fintype α]
  [DecidableEq α]
  {B : Set (ConfigSpace α)} :
-- imply
  rdc_DoubleCover (∅ : Set (ConfigSpace α)) B := by
-- proof
  apply StatMech.rdc_doubleCover_empty_left B

/--
[rdc_reimer_wprob_core_of_doubleCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubleCoverClose.lean)
-/
@[path]
private lemma rdc_reimer_wprob_core_of_doubleCover_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rdc_DoubleCoverAll) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.rdc_reimer_wprob_core_of_doubleCover h

/--
[rdc_reimer_inequality_of_doubleCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubleCoverClose.lean)
-/
@[path]
private lemma rdc_reimer_inequality_of_doubleCover_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (h : rdc_DoubleCoverAll)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.rdc_reimer_inequality_of_doubleCover h hp A B


-- created on 2026-10-23
