/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Topology.Order.Compact
public import Def.MeasureTheory.OptimalTransport.Kantorovich.Part2

public section

section

open MeasureTheory

open scoped BoundedContinuousFunction CompactlySupported ENNReal

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/-- ENNReal subtraction reverses strict inequality on compacta: helper for outer regularity. -/
theorem ennreal_sub_lt_of_lt {a b r : ENNReal}
    (ha : a ≠ ∞) (hb : b ≠ ∞) (hr : r ≠ ∞) (hbr : b < r) (hra : r ≤ a) :
    a - r < a - b := by
  have hba : b ≤ a := hbr.le.trans hra
  have h1 : (a - r).toReal < (a - b).toReal := by
    rw [ENNReal.toReal_sub_of_le hra ha, ENNReal.toReal_sub_of_le hba ha]
    have hbr' : b.toReal < r.toReal := (ENNReal.toReal_lt_toReal hb hr).mpr hbr
    linarith
  have h2 : a - r ≠ ∞ := ne_top_of_le_ne_top ha tsub_le_self
  have h3 : a - b ≠ ∞ := ne_top_of_le_ne_top ha tsub_le_self
  exact (ENNReal.toReal_lt_toReal h2 h3).mp h1

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted
end
