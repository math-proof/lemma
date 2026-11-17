/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/ImageNull.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Topology.Bases
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.Topology.NhdsWithin
open MeasureTheory

/-!
# Images of locally null sets

A set in a second-countable space whose image is locally null has null image.
-/

public section


namespace MathlibExt.MeasureTheory

variable {X Y : Type*} [TopologicalSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y]
variable {μ : Measure Y} {f : X → Y} {s : Set X}
end MathlibExt.MeasureTheory
