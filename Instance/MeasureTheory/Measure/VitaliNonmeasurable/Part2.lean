/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/VitaliNonmeasurable.lean -/

/-
  Author: Muse Code powered by Meta Muse Spark
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Def.MeasureTheory.Measure.VitaliNonmeasurable.Part2
/-!
# Vitali non-measurable set

Vitali's existence of a subset of `ℝ` that is not Lebesgue measurable,
via choice of representatives in `[0, 1]` for translation by rationals.
-/


namespace MeasureTheory

instance : Infinite RatIoo := RatIoo_infinite.to_subtype

end MeasureTheory
