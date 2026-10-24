/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/ImageNull.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Topology.Bases
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.Topology.NhdsWithin

/-!
# Images of locally null sets

A set in a second-countable space whose image is locally null has null image.
-/

open MeasureTheory

namespace MathlibExt.MeasureTheory

variable {X Y : Type*} [TopologicalSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y]
variable {μ : Measure Y} {f : X → Y} {s : Set X}
end MathlibExt.MeasureTheory
