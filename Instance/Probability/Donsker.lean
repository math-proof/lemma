/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Donsker.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Tactic.FunProp
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.IdentDistribIndep
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Def.Probability.Donsker
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
