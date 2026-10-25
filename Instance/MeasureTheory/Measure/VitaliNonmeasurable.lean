/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/VitaliNonmeasurable.lean -/

/-
  Author: Muse Code powered by Meta Muse Spark
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Def.MeasureTheory.Measure.VitaliNonmeasurable
/-!
# Vitali non-measurable set

Vitali's existence of a subset of `ℝ` that is not Lebesgue measurable,
via choice of representatives in `[0, 1]` for translation by rationals.
-/


namespace MeasureTheory

instance : Countable RatIcc :=
  inferInstanceAs (Countable { q : Rat // (-1 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) ≤ (1 : ℝ) })

instance : Countable RatIoo :=
  inferInstanceAs (Countable { q : Rat // 0 < q ∧ q < 1 })

end MeasureTheory
