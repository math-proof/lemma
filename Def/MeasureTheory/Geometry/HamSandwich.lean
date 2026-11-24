module
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Theorem.Topology.Homotopy.BorsukUlam.Part11
public import Theorem.Set.Homotopy.BorsukUlam
public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Order.OrderClosed
open MeasureTheory
open Metric
open scoped InnerProductSpace MeasureTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/HamSandwich.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
namespace MathlibExt.MeasureTheory.Geometry.HamSandwichWanted

/-- Tail projection `EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin n)`,
dropping the `0`-th (head) coordinate. -/
def hsTail {n : ℕ} (u : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j => u (Fin.succ j)

end MathlibExt.MeasureTheory.Geometry.HamSandwichWanted
