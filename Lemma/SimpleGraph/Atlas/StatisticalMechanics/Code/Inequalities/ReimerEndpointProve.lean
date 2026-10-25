import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerEndpointProve.Part3
open Finset MeasureTheory StatMech


/--
[disjoint_leftBlock_rightBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma disjoint_leftBlock_rightBlock_eq :
-- imply
  Disjoint (leftBlock (α := α)) (rightBlock (α := α)) := by
-- proof
  apply StatMech.disjoint_leftBlock_rightBlock

/--
[mem_leftEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma mem_leftEvent_eq
  {A : Set (ConfigSpace α)}
  {ω : ConfigSpace (α ⊕ α)} :
-- imply
  ω ∈ leftEvent A ↔ leftCfg ω ∈ A := by
-- proof
  apply StatMech.mem_leftEvent

/--
[mem_rightEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma mem_rightEvent_eq
  {B : Set (ConfigSpace α)}
  {ω : ConfigSpace (α ⊕ α)} :
-- imply
  ω ∈ rightEvent B ↔ rightCfg ω ∈ B := by
-- proof
  apply StatMech.mem_rightEvent

/--
[leftCfg_eq_of_agreeOn_leftBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma leftCfg_eq_of_agreeOn_leftBlock_eq
  {ω ω' : ConfigSpace (α ⊕ α)}
-- given
  (h : agreeOn (leftBlock (α := α)) ω ω') :
-- imply
  leftCfg ω' = leftCfg ω := by
-- proof
  apply StatMech.leftCfg_eq_of_agreeOn_leftBlock h

/--
[rightCfg_eq_of_agreeOn_rightBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma rightCfg_eq_of_agreeOn_rightBlock_eq
  {ω ω' : ConfigSpace (α ⊕ α)}
-- given
  (h : agreeOn (rightBlock (α := α)) ω ω') :
-- imply
  rightCfg ω' = rightCfg ω := by
-- proof
  apply StatMech.rightCfg_eq_of_agreeOn_rightBlock h

/--
[dependsOn_leftEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma dependsOn_leftEvent_eq
  {A : Set (ConfigSpace α)} :
-- imply
  DependsOn (leftEvent A) (leftBlock (α := α)) := by
-- proof
  apply StatMech.dependsOn_leftEvent A

/--
[dependsOn_rightEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma dependsOn_rightEvent_eq
  {B : Set (ConfigSpace α)} :
-- imply
  DependsOn (rightEvent B) (rightBlock (α := α)) := by
-- proof
  apply StatMech.dependsOn_rightEvent B

/--
[leftCfg_supportCfg_dbl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma leftCfg_supportCfg_dbl_eq
  [DecidableEq α]
  {S T : Finset α} :
-- imply
  leftCfg (supportCfg (dbl S T)) = supportCfg S := by
-- proof
  apply StatMech.leftCfg_supportCfg_dbl S T

/--
[rightCfg_supportCfg_dbl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma rightCfg_supportCfg_dbl_eq
  [DecidableEq α]
  {S T : Finset α} :
-- imply
  rightCfg (supportCfg (dbl S T)) = supportCfg T := by
-- proof
  apply StatMech.rightCfg_supportCfg_dbl S T

/--
[doubleWeight_apply_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma doubleWeight_apply_inl_eq
  [Fintype α]
  [DecidableEq α]
  {w : α → Bool → ℝ}
  {a : α} :
-- imply
  doubleWeight w (Sum.inl a) = w a := by
-- proof
  apply StatMech.doubleWeight_apply_inl w a

/--
[doubleWeight_apply_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma doubleWeight_apply_inr_eq
  [Fintype α]
  [DecidableEq α]
  {w : α → Bool → ℝ}
  {a : α} :
-- imply
  doubleWeight w (Sum.inr a) = w a := by
-- proof
  apply StatMech.doubleWeight_apply_inr w a

/--
[doubleWeight_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma doubleWeight_prob_eq
  [Fintype α]
  [DecidableEq α]
  {w : α → Bool → ℝ}
-- given
  (hw1 : ∀ x, w x false + w x true = 1) :
-- imply
  ∀ x, doubleWeight w x false + doubleWeight w x true = 1 := by
-- proof
  apply StatMech.doubleWeight_prob hw1

/--
[doubleWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma doubleWeight_nonneg_eq
  [Fintype α]
  [DecidableEq α]
  {w : α → Bool → ℝ}
-- given
  (hw0 : ∀ x b, 0 ≤ w x b) :
-- imply
  ∀ x b, 0 ≤ doubleWeight w x b := by
-- proof
  apply StatMech.doubleWeight_nonneg hw0

/--
[pweight_doubleWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma pweight_doubleWeight_eq
  [Fintype α]
  [DecidableEq α]
  {w : α → Bool → ℝ}
  {ω : ConfigSpace (α ⊕ α)} :
-- imply
  pweight (doubleWeight w) ω = pweight w (leftCfg ω) * pweight w (rightCfg ω) := by
-- proof
  apply StatMech.pweight_doubleWeight w ω

/--
[sum_pweight_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma sum_pweight_eq_one_eq
  [Fintype α]
  [DecidableEq α]
  {w : α → Bool → ℝ}
-- given
  (hw1 : ∀ x, w x false + w x true = 1) :
-- imply
  (∑ b : ConfigSpace α, pweight w b) = 1 := by
-- proof
  apply StatMech.sum_pweight_eq_one hw1

/--
[wprob_leftEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma wprob_leftEvent_eq
  [Fintype α]
  [DecidableEq α]
  {w : α → Bool → ℝ}
  {A : Set (ConfigSpace α)}
-- given
  (hw1 : ∀ x, w x false + w x true = 1) :
-- imply
  wprob (doubleWeight w) (leftEvent A) = wprob w A := by
-- proof
  apply StatMech.wprob_leftEvent w hw1 A

/--
[wprob_rightEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma wprob_rightEvent_eq
  [Fintype α]
  [DecidableEq α]
  {w : α → Bool → ℝ}
  {B : Set (ConfigSpace α)}
-- given
  (hw1 : ∀ x, w x false + w x true = 1) :
-- imply
  wprob (doubleWeight w) (rightEvent B) = wprob w B := by
-- proof
  apply StatMech.wprob_rightEvent w hw1 B

/--
[supportCfg_dbl_mem_leftEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma supportCfg_dbl_mem_leftEvent_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 : Finset (Finset α)}
  {S T : Finset α} :
-- imply
  supportCfg (dbl S T) ∈ leftEvent (familyEvent 𝒜) ↔ S ∈ 𝒜 := by
-- proof
  apply StatMech.supportCfg_dbl_mem_leftEvent 𝒜 S T

/--
[supportCfg_dbl_mem_rightEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma supportCfg_dbl_mem_rightEvent_eq
  [Fintype α]
  [DecidableEq α]
  {ℬ : Finset (Finset α)}
  {S T : Finset α} :
-- imply
  supportCfg (dbl S T) ∈ rightEvent (familyEvent ℬ) ↔ T ∈ ℬ := by
-- proof
  apply StatMech.supportCfg_dbl_mem_rightEvent ℬ S T

/--
[reimer_wprob_doubled_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma reimer_wprob_doubled_split_eq
  [Fintype α]
  [DecidableEq α]
  {φ : (α ⊕ α) → Bool → ℝ}
  {A B : Set (ConfigSpace α)}
-- given
  (hφ1 : ∀ x, φ x false + φ x true = 1) :
-- imply
  wprob φ (disjointOccurrence (leftEvent A) (rightEvent B)) = wprob φ (leftEvent A) * wprob φ (rightEvent B) := by
-- proof
  apply StatMech.reimer_wprob_doubled_split φ hφ1 A B

/--
[reimer_wprob_doubled_familyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma reimer_wprob_doubled_familyEvent_eq
  [Fintype α]
  [DecidableEq α]
  {φ : (α ⊕ α) → Bool → ℝ}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (hφ1 : ∀ x, φ x false + φ x true = 1) :
-- imply
  wprob φ (disjointOccurrence (leftEvent (familyEvent 𝒜)) (rightEvent (familyEvent ℬ))) = wprob φ (leftEvent (familyEvent 𝒜)) * wprob φ (rightEvent (familyEvent ℬ)) := by
-- proof
  apply StatMech.reimer_wprob_doubled_familyEvent φ hφ1 𝒜 ℬ

/--
[familyEvent_boxDoubled_subset_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma familyEvent_boxDoubled_subset_inter_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  familyEvent (boxDoubled 𝒜 ℬ) ⊆ leftEvent (familyEvent 𝒜) ∩ rightEvent (familyEvent ℬ) := by
-- proof
  apply StatMech.familyEvent_boxDoubled_subset_inter 𝒜 ℬ

/--
[wprob_familyEvent_boxDoubled_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma wprob_familyEvent_boxDoubled_le_eq
  [Fintype α]
  [DecidableEq α]
  {φ : (α ⊕ α) → Bool → ℝ}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (hφ0 : ∀ x b, 0 ≤ φ x b)
  (hφ1 : ∀ x, φ x false + φ x true = 1) :
-- imply
  wprob φ (familyEvent (boxDoubled 𝒜 ℬ)) ≤ wprob φ (leftEvent (familyEvent 𝒜)) * wprob φ (rightEvent (familyEvent ℬ)) := by
-- proof
  apply StatMech.wprob_familyEvent_boxDoubled_le φ hφ0 hφ1 𝒜 ℬ

/--
[fwt_doubleWeight_dbl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma fwt_doubleWeight_dbl_eq
  [Fintype α]
  [DecidableEq α]
  {w : α → Bool → ℝ}
  {S T : Finset α} :
-- imply
  fwt (doubleWeight w) (dbl S T) = fwt w S * fwt w T := by
-- proof
  apply StatMech.fwt_doubleWeight_dbl w S T

/--
[fmarg_boxDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma fmarg_boxDoubled_eq
  [Fintype α]
  [DecidableEq α]
  {w : α → Bool → ℝ}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  fmarg (doubleWeight w) (boxDoubled 𝒜 ℬ) = wdpairs w 𝒜 ℬ := by
-- proof
  apply StatMech.fmarg_boxDoubled w 𝒜 ℬ

/--
[wprob_familyEvent_boxDoubled_eq_wdpairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma wprob_familyEvent_boxDoubled_eq_wdpairs_eq
  [Fintype α]
  [DecidableEq α]
  {w : α → Bool → ℝ}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  wprob (doubleWeight w) (familyEvent (boxDoubled 𝒜 ℬ)) = wdpairs w 𝒜 ℬ := by
-- proof
  apply StatMech.wprob_familyEvent_boxDoubled_eq_wdpairs w 𝒜 ℬ

/--
[wdpairs_le_mul_of_doubled_independence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean)
-/
@[path]
private lemma wdpairs_le_mul_of_doubled_independence_eq
  [Fintype α]
  [DecidableEq α]
  {w : α → Bool → ℝ}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (hw0 : ∀ x b, 0 ≤ w x b)
  (hw1 : ∀ x, w x false + w x true = 1) :
-- imply
  wdpairs w 𝒜 ℬ ≤ fmarg w 𝒜 * fmarg w ℬ := by
-- proof
  apply StatMech.wdpairs_le_mul_of_doubled_independence hw0 hw1 𝒜 ℬ


-- created on 2026-10-23
