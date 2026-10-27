import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteHardField.Part3
open Filter StatMech StatMech.Exact3D


/--
[finiteFactorNumeratorSummand_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean)
-/
@[path]
private lemma finiteFactorNumeratorSummand_tendsto_eq
  {base obs limitFactor : α → ℝ}
  {factor : ℝ → α → ℝ}
  {a : α}
-- given
  (hfactor : Tendsto (fun H : ℝ => factor H a) atTop (𝓝 (limitFactor a))) :
-- imply
  Tendsto (fun H : ℝ => base a * factor H a * obs a) atTop (𝓝 (base a * limitFactor a * obs a)) := by
-- proof
  apply StatMech.Exact3D.finiteFactorNumeratorSummand_tendsto base obs limitFactor factor a hfactor

/--
[finiteFactorDenominatorSummand_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean)
-/
@[path]
private lemma finiteFactorDenominatorSummand_tendsto_eq
  {base limitFactor : α → ℝ}
  {factor : ℝ → α → ℝ}
  {a : α}
-- given
  (hfactor : Tendsto (fun H : ℝ => factor H a) atTop (𝓝 (limitFactor a))) :
-- imply
  Tendsto (fun H : ℝ => base a * factor H a) atTop (𝓝 (base a * limitFactor a)) := by
-- proof
  apply StatMech.Exact3D.finiteFactorDenominatorSummand_tendsto base limitFactor factor a hfactor

/--
[finiteFactorNumerator_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean)
-/
@[path]
private lemma finiteFactorNumerator_tendsto_eq
  {s : Finset α}
  {base obs limitFactor : α → ℝ}
  {factor : ℝ → α → ℝ}
-- given
  (hfactor : ∀ a, a ∈ s → Tendsto (fun H : ℝ => factor H a) atTop (𝓝 (limitFactor a))) :
-- imply
  Tendsto (fun H : ℝ => finiteFactorNumerator s base obs factor H) atTop (𝓝 (finiteFactorLimitNumerator s base obs limitFactor)) := by
-- proof
  apply StatMech.Exact3D.finiteFactorNumerator_tendsto s base obs limitFactor factor hfactor

/--
[finiteFactorDenominator_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean)
-/
@[path]
private lemma finiteFactorDenominator_tendsto_eq
  {s : Finset α}
  {base limitFactor : α → ℝ}
  {factor : ℝ → α → ℝ}
-- given
  (hfactor : ∀ a, a ∈ s → Tendsto (fun H : ℝ => factor H a) atTop (𝓝 (limitFactor a))) :
-- imply
  Tendsto (fun H : ℝ => finiteFactorDenominator s base factor H) atTop (𝓝 (finiteFactorLimitDenominator s base limitFactor)) := by
-- proof
  apply StatMech.Exact3D.finiteFactorDenominator_tendsto s base limitFactor factor hfactor

/--
[finiteFactorRatio_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean)
-/
@[path]
private lemma finiteFactorRatio_tendsto_eq
  {s : Finset α}
  {base obs limitFactor : α → ℝ}
  {factor : ℝ → α → ℝ}
-- given
  (hfactor : ∀ a, a ∈ s → Tendsto (fun H : ℝ => factor H a) atTop (𝓝 (limitFactor a)))
  (hden : finiteFactorLimitDenominator s base limitFactor ≠ 0) :
-- imply
  Tendsto (fun H : ℝ => finiteFactorRatio s base obs factor H) atTop (𝓝 (finiteFactorLimitRatio s base obs limitFactor)) := by
-- proof
  apply StatMech.Exact3D.finiteFactorRatio_tendsto s base obs limitFactor factor hfactor hden

/--
[tendsto_exp_neg_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean)
-/
@[path]
private lemma tendsto_exp_neg_atTop_eq :
-- imply
  Tendsto (fun H : ℝ => Real.exp (-H)) atTop (𝓝 0) := by
-- proof
  apply StatMech.Exact3D.tendsto_exp_neg_atTop

/--
[hardFieldFactor_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean)
-/
@[path]
private lemma hardFieldFactor_tendsto_eq
  [DecidablePred good]
  {a : α}
-- given
  (good : α → Prop) :
-- imply
  Tendsto (fun H : ℝ => hardFieldFactor good H a) atTop (𝓝 (if good a then 1 else 0)) := by
-- proof
  apply StatMech.Exact3D.hardFieldFactor_tendsto good a

/--
[hardFieldNumeratorSummand_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean)
-/
@[path]
private lemma hardFieldNumeratorSummand_tendsto_eq
  [DecidablePred good]
  {base obs : α → ℝ}
  {a : α}
-- given
  (good : α → Prop) :
-- imply
  Tendsto (fun H : ℝ => base a * hardFieldFactor good H a * obs a) atTop (𝓝 (if good a then base a * obs a else 0)) := by
-- proof
  apply StatMech.Exact3D.hardFieldNumeratorSummand_tendsto good base obs a

/--
[hardFieldDenominatorSummand_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean)
-/
@[path]
private lemma hardFieldDenominatorSummand_tendsto_eq
  [DecidablePred good]
  {base : α → ℝ}
  {a : α}
-- given
  (good : α → Prop) :
-- imply
  Tendsto (fun H : ℝ => base a * hardFieldFactor good H a) atTop (𝓝 (if good a then base a else 0)) := by
-- proof
  apply StatMech.Exact3D.hardFieldDenominatorSummand_tendsto good base a

/--
[hardFieldNumerator_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean)
-/
@[path]
private lemma hardFieldNumerator_tendsto_eq
  {s : Finset α}
  [DecidablePred good]
  {base obs : α → ℝ}
-- given
  (good : α → Prop) :
-- imply
  Tendsto (fun H : ℝ => hardFieldNumerator s good base obs H) atTop (𝓝 (hardFieldLimitNumerator s good base obs)) := by
-- proof
  apply StatMech.Exact3D.hardFieldNumerator_tendsto s good base obs

/--
[hardFieldDenominator_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean)
-/
@[path]
private lemma hardFieldDenominator_tendsto_eq
  {s : Finset α}
  [DecidablePred good]
  {base : α → ℝ}
-- given
  (good : α → Prop) :
-- imply
  Tendsto (fun H : ℝ => hardFieldDenominator s good base H) atTop (𝓝 (hardFieldLimitDenominator s good base)) := by
-- proof
  apply StatMech.Exact3D.hardFieldDenominator_tendsto s good base

/--
[hardFieldRatio_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean)
-/
@[path]
private lemma hardFieldRatio_tendsto_eq
  {s : Finset α}
  [DecidablePred good]
  {base obs : α → ℝ}
-- given
  (good : α → Prop)
  (hden : hardFieldLimitDenominator s good base ≠ 0) :
-- imply
  Tendsto (fun H : ℝ => hardFieldRatio s good base obs H) atTop (𝓝 (hardFieldLimitRatio s good base obs)) := by
-- proof
  apply StatMech.Exact3D.hardFieldRatio_tendsto s good base obs hden

/--
[hardFieldLimitNumerator_eq_filter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean)
-/
@[path]
private lemma hardFieldLimitNumerator_eq_filter_eq
  {s : Finset α}
  [DecidablePred good]
  {base obs : α → ℝ}
-- given
  (good : α → Prop) :
-- imply
  hardFieldLimitNumerator s good base obs = ∑ a ∈ s.filter good, base a * obs a := by
-- proof
  apply StatMech.Exact3D.hardFieldLimitNumerator_eq_filter s good base obs

/--
[hardFieldLimitDenominator_eq_filter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean)
-/
@[path]
private lemma hardFieldLimitDenominator_eq_filter_eq
  {s : Finset α}
  [DecidablePred good]
  {base : α → ℝ}
-- given
  (good : α → Prop) :
-- imply
  hardFieldLimitDenominator s good base = ∑ a ∈ s.filter good, base a := by
-- proof
  apply StatMech.Exact3D.hardFieldLimitDenominator_eq_filter s good base

/--
[hardFieldLimitDenominator_pos_of_exists_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean)
-/
@[path]
private lemma hardFieldLimitDenominator_pos_of_exists_pos_eq
  {s : Finset α}
  [DecidablePred good]
  {base : α → ℝ}
-- given
  (good : α → Prop)
  (hnonneg : ∀ a, a ∈ s → good a → 0 ≤ base a)
  (hpos : ∃ a, a ∈ s ∧ good a ∧ 0 < base a) :
-- imply
  0 < hardFieldLimitDenominator s good base := by
-- proof
  apply StatMech.Exact3D.hardFieldLimitDenominator_pos_of_exists_pos s good base hnonneg hpos

/--
[hardFieldLimitDenominator_ne_zero_of_exists_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean)
-/
@[path]
private lemma hardFieldLimitDenominator_ne_zero_of_exists_pos_eq
  {s : Finset α}
  [DecidablePred good]
  {base : α → ℝ}
-- given
  (good : α → Prop)
  (hnonneg : ∀ a, a ∈ s → good a → 0 ≤ base a)
  (hpos : ∃ a, a ∈ s ∧ good a ∧ 0 < base a) :
-- imply
  hardFieldLimitDenominator s good base ≠ 0 := by
-- proof
  apply StatMech.Exact3D.hardFieldLimitDenominator_ne_zero_of_exists_pos s good base hnonneg hpos

/--
[countHardFieldFactor_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean)
-/
@[path]
private lemma countHardFieldFactor_tendsto_eq
  {penalty : α → ℕ}
  {scale : ℝ}
  {a : α}
-- given
  (hscale : 0 < scale) :
-- imply
  Tendsto (fun H : ℝ => countHardFieldFactor penalty scale H a) atTop (𝓝 (countHardFieldLimitFactor penalty a)) := by
-- proof
  apply StatMech.Exact3D.countHardFieldFactor_tendsto penalty hscale a

/--
[countHardFieldRatio_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean)
-/
@[path]
private lemma countHardFieldRatio_tendsto_eq
  {s : Finset α}
  {penalty : α → ℕ}
  {scale : ℝ}
  {base obs : α → ℝ}
-- given
  (hscale : 0 < scale)
  (hden : finiteFactorLimitDenominator s base (countHardFieldLimitFactor penalty) ≠ 0) :
-- imply
  Tendsto (fun H : ℝ => finiteFactorRatio s base obs (countHardFieldFactor penalty scale) H) atTop (𝓝 (finiteFactorLimitRatio s base obs (countHardFieldLimitFactor penalty))) := by
-- proof
  apply StatMech.Exact3D.countHardFieldRatio_tendsto s penalty hscale base obs hden

/--
[countHardFieldLimitDenominator_pos_of_exists_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean)
-/
@[path]
private lemma countHardFieldLimitDenominator_pos_of_exists_pos_eq
  {s : Finset α}
  {penalty : α → ℕ}
  {base : α → ℝ}
-- given
  (hnonneg : ∀ a, a ∈ s → penalty a = 0 → 0 ≤ base a)
  (hpos : ∃ a, a ∈ s ∧ penalty a = 0 ∧ 0 < base a) :
-- imply
  0 < finiteFactorLimitDenominator s base (countHardFieldLimitFactor penalty) := by
-- proof
  apply StatMech.Exact3D.countHardFieldLimitDenominator_pos_of_exists_pos s penalty base hnonneg hpos

/--
[countHardFieldLimitDenominator_ne_zero_of_exists_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean)
-/
@[path]
private lemma countHardFieldLimitDenominator_ne_zero_of_exists_pos_eq
  {s : Finset α}
  {penalty : α → ℕ}
  {base : α → ℝ}
-- given
  (hnonneg : ∀ a, a ∈ s → penalty a = 0 → 0 ≤ base a)
  (hpos : ∃ a, a ∈ s ∧ penalty a = 0 ∧ 0 < base a) :
-- imply
  finiteFactorLimitDenominator s base (countHardFieldLimitFactor penalty) ≠ 0 := by
-- proof
  apply StatMech.Exact3D.countHardFieldLimitDenominator_ne_zero_of_exists_pos s penalty base hnonneg hpos


-- created on 2026-10-23
