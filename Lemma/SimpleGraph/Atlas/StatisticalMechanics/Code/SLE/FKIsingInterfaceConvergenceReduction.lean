import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.SLE.FKIsingInterfaceConvergenceReduction
open Filter MeasureTheory Set Topology StatMech StatMech.SLE


/--
[weaklySequentiallyPrecompact_of_tight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/FKIsingInterfaceConvergenceReduction.lean)
-/
@[path]
private lemma weaklySequentiallyPrecompact_of_tight_eq
  [MeasurableSpace X]
  [TopologicalSpace X]
  [PolishSpace X]
  [BorelSpace X]
-- given
  (laws : Nat -> ProbabilityMeasure X)
  (hTight : IsTightMeasureSet {mu : Measure X | exists n, mu = (laws n : Measure X)}) :
-- imply
  IsWeaklySequentiallyPrecompact laws := by
-- proof
  apply StatMech.SLE.weaklySequentiallyPrecompact_of_tight laws hTight

/--
[tendsto_of_weaklySequentiallyPrecompact_of_subsequential_limits_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/FKIsingInterfaceConvergenceReduction.lean)
-/
@[path]
private lemma tendsto_of_weaklySequentiallyPrecompact_of_subsequential_limits_eq_eq
  [MeasurableSpace X]
  [TopologicalSpace X]
  [OpensMeasurableSpace X]
  {target : ProbabilityMeasure X}
-- given
  (laws : Nat -> ProbabilityMeasure X)
  (hcompact : IsWeaklySequentiallyPrecompact laws)
  (hunique : forall (phi psi : Nat -> Nat) (limit : ProbabilityMeasure X), StrictMono phi -> StrictMono psi -> Tendsto (fun n => laws (phi (psi n))) atTop (nhds limit) -> limit = target) :
-- imply
  Tendsto laws atTop (nhds target) := by
-- proof
  apply StatMech.SLE.tendsto_of_weaklySequentiallyPrecompact_of_subsequential_limits_eq laws target hcompact hunique

/--
[tendsto_of_tight_of_subsequential_limits_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/FKIsingInterfaceConvergenceReduction.lean)
-/
@[path]
private lemma tendsto_of_tight_of_subsequential_limits_eq_eq
  [MeasurableSpace X]
  [TopologicalSpace X]
  [PolishSpace X]
  [BorelSpace X]
  {target : ProbabilityMeasure X}
-- given
  (laws : Nat -> ProbabilityMeasure X)
  (hTight : IsTightMeasureSet {mu : Measure X | exists n, mu = (laws n : Measure X)})
  (hunique : forall (phi psi : Nat -> Nat) (limit : ProbabilityMeasure X), StrictMono phi -> StrictMono psi -> Tendsto (fun n => laws (phi (psi n))) atTop (nhds limit) -> limit = target) :
-- imply
  Tendsto laws atTop (nhds target) := by
-- proof
  apply StatMech.SLE.tendsto_of_tight_of_subsequential_limits_eq laws target hTight hunique

/--
[tendsto_of_tight_of_unique_subsequential_criterion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/FKIsingInterfaceConvergenceReduction.lean)
-/
@[path]
private lemma tendsto_of_tight_of_unique_subsequential_criterion_eq
  [MeasurableSpace X]
  [TopologicalSpace X]
  [PolishSpace X]
  [BorelSpace X]
  {target : ProbabilityMeasure X}
-- given
  (laws : Nat -> ProbabilityMeasure X)
  (criterion : ProbabilityMeasure X -> Prop)
  (hTight : IsTightMeasureSet {mu : Measure X | exists n, mu = (laws n : Measure X)})
  (hlimits : forall (phi psi : Nat -> Nat) (limit : ProbabilityMeasure X), StrictMono phi -> StrictMono psi -> Tendsto (fun n => laws (phi (psi n))) atTop (nhds limit) -> criterion limit)
  (hunique : forall limit, criterion limit -> limit = target) :
-- imply
  Tendsto laws atTop (nhds target) := by
-- proof
  apply StatMech.SLE.tendsto_of_tight_of_unique_subsequential_criterion laws target criterion hTight hlimits hunique


-- created on 2026-10-23
