import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
open StatMech


/--
[IsIncreasing.compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/IncreasingEvent.lean)
-/
@[path]
private lemma compl_eq
  {A : Set (ConfigSpace E)}
-- given
  (hA : IsIncreasing A) :
-- imply
  IsDecreasing Aᶜ := by
-- proof
  apply StatMech.IsIncreasing.compl hA

/--
[IsDecreasing.compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/IncreasingEvent.lean)
-/
@[path]
private lemma compl_eq_2
  {A : Set (ConfigSpace E)}
-- given
  (hA : IsDecreasing A) :
-- imply
  IsIncreasing Aᶜ := by
-- proof
  apply StatMech.IsDecreasing.compl hA

/--
[IsIncreasing.inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/IncreasingEvent.lean)
-/
@[path]
private lemma inter_eq
  {A B : Set (ConfigSpace E)}
-- given
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  IsIncreasing (A ∩ B) := by
-- proof
  apply StatMech.IsIncreasing.inter hA hB

/--
[IsIncreasing.union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/IncreasingEvent.lean)
-/
@[path]
private lemma union_eq
  {A B : Set (ConfigSpace E)}
-- given
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  IsIncreasing (A ∪ B) := by
-- proof
  apply StatMech.IsIncreasing.union hA hB

/--
[isIncreasing_iInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/IncreasingEvent.lean)
-/
@[path]
private lemma isIncreasing_iInter_eq
  {A : ι → Set (ConfigSpace E)}
-- given
  (hA : ∀ i, IsIncreasing (A i)) :
-- imply
  IsIncreasing (⋂ i, A i) := by
-- proof
  apply StatMech.isIncreasing_iInter hA

/--
[IsIncreasing.indicator_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/IncreasingEvent.lean)
-/
@[path]
private lemma indicator_monotone_eq
  {A : Set (ConfigSpace E)}
-- given
  (hA : IsIncreasing A) :
-- imply
  Monotone (A.indicator (fun _ => (1 : ℝ))) := by
-- proof
  apply StatMech.IsIncreasing.indicator_monotone hA

/--
[isIncreasing_iff_indicator_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/IncreasingEvent.lean)
-/
@[path]
private lemma isIncreasing_iff_indicator_monotone_eq
  {A : Set (ConfigSpace E)} :
-- imply
  IsIncreasing A ↔ Monotone (A.indicator (fun _ => (1 : ℝ))) := by
-- proof
  apply StatMech.isIncreasing_iff_indicator_monotone

/--
[indicator_nonneg'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/IncreasingEvent.lean)
-/
@[path]
private lemma indicator_nonneg'_eq
  {A : Set (ConfigSpace E)} :
-- imply
  (0 : ConfigSpace E → ℝ) ≤ A.indicator (fun _ => (1 : ℝ)) := by
-- proof
  apply StatMech.indicator_nonneg' A

/--
[FKGLatticeCondition.of_logModular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/IncreasingEvent.lean)
-/
@[path]
private lemma of_logModular_eq
  {π : ConfigSpace E → ℝ}
-- given
  (h : ∀ ω ω', π ω * π ω' = π (ω ⊔ ω') * π (ω ⊓ ω')) :
-- imply
  FKGLatticeCondition π := by
-- proof
  apply StatMech.FKGLatticeCondition.of_logModular h


-- created on 2026-10-23
