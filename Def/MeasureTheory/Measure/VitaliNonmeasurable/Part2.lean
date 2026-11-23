/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/VitaliNonmeasurable.lean -/

/-
  Author: Muse Code powered by Meta Muse Spark
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Instance.MeasureTheory.Measure.VitaliNonmeasurable

@[expose] public section

/-!
# Vitali non-measurable set

Vitali's existence of a subset of `ℝ` that is not Lebesgue measurable,
via choice of representatives in `[0, 1]` for translation by rationals.
-/


namespace MeasureTheory

noncomputable def FamIcc (q : RatIcc) : Set ℝ := vitaliTranslate (q.val : ℝ)

noncomputable def FamIoo (q : RatIoo) : Set ℝ := vitaliTranslate (q.val : ℝ)

end MeasureTheory
