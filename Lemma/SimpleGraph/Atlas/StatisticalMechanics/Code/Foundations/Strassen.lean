import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Foundations.Strassen
open MeasureTheory StatMech StatMech.MonotoneCoupling


/--
[total_mass_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Strassen.lean)
-/
@[path]
private lemma total_mass_eq_eq
  {μ ν : Measure (ConfigSpace E)}
-- given
  (h : MonotoneCoupling μ ν κ) :
-- imply
  μ Set.univ = ν Set.univ := by
-- proof
  apply StatMech.MonotoneCoupling.total_mass_eq h

/--
[isFiniteMeasure_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Strassen.lean)
-/
@[path]
private lemma isFiniteMeasure_left_eq
  {μ ν : Measure (ConfigSpace E)}
  [IsFiniteMeasure κ]
-- given
  (h : MonotoneCoupling μ ν κ) :
-- imply
  IsFiniteMeasure μ := by
-- proof
  apply StatMech.MonotoneCoupling.isFiniteMeasure_left h

/--
[isFiniteMeasure_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Strassen.lean)
-/
@[path]
private lemma isFiniteMeasure_right_eq
  {μ ν : Measure (ConfigSpace E)}
  [IsFiniteMeasure κ]
-- given
  (h : MonotoneCoupling μ ν κ) :
-- imply
  IsFiniteMeasure ν := by
-- proof
  apply StatMech.MonotoneCoupling.isFiniteMeasure_right h

/--
[isProbabilityMeasure_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Strassen.lean)
-/
@[path]
private lemma isProbabilityMeasure_left_eq
  {μ ν : Measure (ConfigSpace E)}
  [IsProbabilityMeasure κ]
-- given
  (h : MonotoneCoupling μ ν κ) :
-- imply
  IsProbabilityMeasure μ := by
-- proof
  apply StatMech.MonotoneCoupling.isProbabilityMeasure_left h

/--
[isProbabilityMeasure_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Strassen.lean)
-/
@[path]
private lemma isProbabilityMeasure_right_eq
  {μ ν : Measure (ConfigSpace E)}
  [IsProbabilityMeasure κ]
-- given
  (h : MonotoneCoupling μ ν κ) :
-- imply
  IsProbabilityMeasure ν := by
-- proof
  apply StatMech.MonotoneCoupling.isProbabilityMeasure_right h

/--
[measurableSet_orderSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Strassen.lean)
-/
@[path]
private lemma measurableSet_orderSet_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  MeasurableSet (orderSet E) := by
-- proof
  apply StatMech.measurableSet_orderSet

/--
[stochasticallyDominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Strassen.lean)
-/
@[path]
private lemma stochasticallyDominated_eq
  [Fintype E]
  [DecidableEq E]
  {μ ν : Measure (ConfigSpace E)}
  [IsFiniteMeasure κ]
-- given
  (h : MonotoneCoupling μ ν κ) :
-- imply
  μ ≼ ν := by
-- proof
  apply StatMech.MonotoneCoupling.stochasticallyDominated h

/--
[stochasticallyDominated_of_exists_monotoneCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Strassen.lean)
-/
@[path]
private lemma stochasticallyDominated_of_exists_monotoneCoupling_eq
  [Fintype E]
  [DecidableEq E]
  {μ ν : Measure (ConfigSpace E)}
-- given
  (h : ∃ κ : Measure (ConfigSpace E × ConfigSpace E), IsFiniteMeasure κ ∧ MonotoneCoupling μ ν κ) :
-- imply
  μ ≼ ν := by
-- proof
  apply StatMech.stochasticallyDominated_of_exists_monotoneCoupling h


-- created on 2026-10-23
