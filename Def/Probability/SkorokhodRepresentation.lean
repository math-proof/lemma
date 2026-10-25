/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/SkorokhodRepresentation.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.CDF
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.UniformSpace.Uniformizable


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
