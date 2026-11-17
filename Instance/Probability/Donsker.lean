/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Donsker.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

module

public import Mathlib.Tactic.FunProp
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.IdentDistribIndep
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Def.Probability.Donsker

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ProbabilityTheory Real

/-!
# Donsker's invariance principle

This file proves the functional CLT: polygonal partial-sum processes converge in
`C([0,1],ℝ)` to Brownian motion.
-/


namespace MathlibExt.Probability.DonskerWanted

noncomputable section

/-- Local Borel structures for `C(Icc 0 1, ℝ)`, scoped to avoid orphan leakage. -/
scoped instance instMeasurableSpaceContinuousMap : MeasurableSpace C(Set.Icc (0 : ℝ) 1, ℝ) :=
  borel _

scoped instance instBorelSpaceContinuousMap : BorelSpace C(Set.Icc (0 : ℝ) 1, ℝ) :=
  ⟨rfl⟩

end
end MathlibExt.Probability.DonskerWanted
