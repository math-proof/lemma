import Mathlib
import sympy.Basic
import sympy.atlas.MeasureTheory.Measure.ImageNull
open MeasureTheory
open MathlibExt.MeasureTheory


/--
[measure_image_null_of_locally_null](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/ImageNull.lean)
-/
@[path]
private lemma measure_image_null_of_locally_null_eq
  [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace Y]
  {μ : Measure Y}
  {f : X → Y}
  {s : Set X}
-- given
  (h : ∀ x ∈ s, ∃ V ∈ nhds x, μ (f '' (V ∩ s)) = 0) :
-- imply
  μ (f '' s) = 0 := by
-- proof
  apply MathlibExt.MeasureTheory.measure_image_null_of_locally_null h


-- created on 2026-10-20
