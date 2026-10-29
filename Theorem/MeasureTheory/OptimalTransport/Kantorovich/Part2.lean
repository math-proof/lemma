/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.Order.Compact
import Def.MeasureTheory.OptimalTransport.Kantorovich.Part2


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
