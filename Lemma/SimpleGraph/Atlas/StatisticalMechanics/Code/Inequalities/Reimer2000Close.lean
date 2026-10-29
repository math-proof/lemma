import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer2000Close.Part5
open Finset MeasureTheory StatMech


/--
[swapGlue_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer2000Close.lean)
-/
@[path]
private lemma swapGlue_apply_eq
  [Fintype α]
  [DecidableEq α]
  {S : α → Bool}
  {ω τ : ConfigSpace α}
  {a : α} :
-- imply
  swapGlue S ω τ a = if S a then τ a else ω a := by
-- proof
  apply StatMech.swapGlue_apply S ω τ a

/--
[swapPair_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer2000Close.lean)
-/
@[path]
private lemma swapPair_weight_eq
  [Fintype α]
  [DecidableEq α]
  {φ : α → Bool → ℝ}
  {S : α → Bool}
  {ω τ : ConfigSpace α} :
-- imply
  pweight φ (swapGlue S ω τ) * pweight φ (swapGlue S τ ω) = pweight φ ω * pweight φ τ := by
-- proof
  apply StatMech.swapPair_weight φ S ω τ

/--
[swapGlue_swapGlue_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer2000Close.lean)
-/
@[path]
private lemma swapGlue_swapGlue_left_eq
  [Fintype α]
  [DecidableEq α]
  {S : α → Bool}
  {ω τ : ConfigSpace α} :
-- imply
  swapGlue S (swapGlue S ω τ) (swapGlue S τ ω) = ω := by
-- proof
  apply StatMech.swapGlue_swapGlue_left S ω τ

/--
[swapGlue_swapGlue_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer2000Close.lean)
-/
@[path]
private lemma swapGlue_swapGlue_right_eq
  [Fintype α]
  [DecidableEq α]
  {S : α → Bool}
  {ω τ : ConfigSpace α} :
-- imply
  swapGlue S (swapGlue S τ ω) (swapGlue S ω τ) = τ := by
-- proof
  apply StatMech.swapGlue_swapGlue_right S ω τ

/--
[swapPair_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer2000Close.lean)
-/
@[path]
private lemma swapPair_fst_eq
  [Fintype α]
  [DecidableEq α]
  {σ : ConfigSpace α × ConfigSpace α → (α → Bool)}
  {p : ConfigSpace α × ConfigSpace α} :
-- imply
  (swapPair σ p).1 = swapGlue (σ p) p.1 p.2 := by
-- proof
  apply StatMech.swapPair_fst σ p

/--
[swapPair_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer2000Close.lean)
-/
@[path]
private lemma swapPair_snd_eq
  [Fintype α]
  [DecidableEq α]
  {σ : ConfigSpace α × ConfigSpace α → (α → Bool)}
  {p : ConfigSpace α × ConfigSpace α} :
-- imply
  (swapPair σ p).2 = swapGlue (σ p) p.2 p.1 := by
-- proof
  apply StatMech.swapPair_snd σ p

/--
[r2k_weightInjection_of_swapInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer2000Close.lean)
-/
@[path]
private lemma r2k_weightInjection_of_swapInjection_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hSI : r2k_SwapInjection A B) :
-- imply
  rpw_WeightInjection A B := by
-- proof
  apply StatMech.r2k_weightInjection_of_swapInjection hSI

/--
[r2k_reimer_wprob_of_swapInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer2000Close.lean)
-/
@[path]
private lemma r2k_reimer_wprob_of_swapInjection_eq
  [Fintype α]
  [DecidableEq α]
  {φ : α → Bool → ℝ}
  {A B : Set (ConfigSpace α)}
-- given
  (hφ0 : ∀ x b, 0 ≤ φ x b)
  (hφ1 : ∀ x, φ x false + φ x true = 1)
  (hSI : r2k_SwapInjection A B) :
-- imply
  wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
-- proof
  apply StatMech.r2k_reimer_wprob_of_swapInjection φ hφ0 hφ1 hSI

/--
[r2k_swapPair_const_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer2000Close.lean)
-/
@[path]
private lemma r2k_swapPair_const_injective_eq
  [Fintype α]
  [DecidableEq α]
  {S₀ : α → Bool} :
-- imply
  Function.Injective (swapPair (fun _ => S₀) : ConfigSpace α × ConfigSpace α → _) := by
-- proof
  apply StatMech.r2k_swapPair_const_injective S₀

/--
[r2k_swapInjection_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer2000Close.lean)
-/
@[path]
private lemma r2k_swapInjection_of_disjoint_support_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S T : Finset α}
-- given
  (hA : DependsOn A (↑S))
  (hB : DependsOn B (↑T))
  (hST : Disjoint S T) :
-- imply
  r2k_SwapInjection A B := by
-- proof
  apply StatMech.r2k_swapInjection_of_disjoint_support hA hB hST

/--
[r2k_swapInjection_of_box_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer2000Close.lean)
-/
@[path]
private lemma r2k_swapInjection_of_box_empty_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hbox : disjointOccurrence A B = ∅) :
-- imply
  r2k_SwapInjection A B := by
-- proof
  apply StatMech.r2k_swapInjection_of_box_empty hbox

/--
[r2k_reimer_wprob_core_of_swapInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer2000Close.lean)
-/
@[path]
private lemma r2k_reimer_wprob_core_of_swapInjection_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : r2k_SwapInjectionAll) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.r2k_reimer_wprob_core_of_swapInjection h

/--
[r2k_reimer_inequality_of_swapInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer2000Close.lean)
-/
@[path]
private lemma r2k_reimer_inequality_of_swapInjection_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype E]
  [DecidableEq E]
  {p : NNReal}
  {A B : Set (ConfigSpace E)}
-- given
  (h : r2k_SwapInjectionAll)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.r2k_reimer_inequality_of_swapInjection h hp A B

/--
[r2k_rbi_box_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer2000Close.lean)
-/
@[path]
private lemma r2k_rbi_box_fst_eq
  [Fintype α]
  [DecidableEq α]
  {ω : ConfigSpace (Fin 2)}
-- given
  (hω : ω ∈ disjointOccurrence rbi_A rbi_B) :
-- imply
  ω 0 = false := by
-- proof
  apply StatMech.r2k_rbi_box_fst hω

/--
[r2k_swapInjection_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer2000Close.lean)
-/
@[path]
private lemma r2k_swapInjection_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  r2k_SwapInjection rbi_A rbi_B := by
-- proof
  apply StatMech.r2k_swapInjection_rbi


-- created on 2026-10-23
