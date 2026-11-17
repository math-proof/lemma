/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/SkorokhodRepresentation.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Probability.CDF
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.Cardinality
public import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

open MeasureTheory

open scoped ENNReal NNReal

namespace MathlibExt.Probability.SkorokhodRepresentationWanted

/-!
# Skorokhod representation theorem

Wishlist coupling weak convergence of Borel probability measures on a Polish space
to almost-sure convergence of random variables on `[0,1]`.
-/

noncomputable def cdfQuantile (ν : Measure ℝ) (u : ℝ) : ℝ :=
  if u ∈ Set.Ioo (0 : ℝ) (1 : ℝ) then sInf {t : ℝ | u ≤ ProbabilityTheory.cdf ν t} else 0

end MathlibExt.Probability.SkorokhodRepresentationWanted
end
