/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/HamSandwich.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import sympy.atlas.Topology.Homotopy.BorsukUlam
import Lemma.Set.Homotopy.BorsukUlam
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.OrderClosed

open MeasureTheory
open Metric
open scoped InnerProductSpace MeasureTheory

namespace MathlibExt.MeasureTheory.Geometry.HamSandwichWanted

/-- Tail projection `EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin n)`,
dropping the `0`-th (head) coordinate. -/
private def hsTail {n : ℕ} (u : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j => u (Fin.succ j)
end MathlibExt.MeasureTheory.Geometry.HamSandwichWanted
namespace MathlibExt.MeasureTheory.Geometry.HamSandwichWanted
end MathlibExt.MeasureTheory.Geometry.HamSandwichWanted
