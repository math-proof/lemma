import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.NumberField.NormalizedPlace
open NumberField


namespace NumberField

/--
[FinitePlace.normalizedAbsoluteValue_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/NormalizedPlace.lean)
-/
@[path]
lemma FinitePlace.normalizedAbsoluteValue_apply
  [Field K] [NumberField K]
  {v : FinitePlace K}
  {x : K} :
-- imply
  v.normalizedAbsoluteValue x = v x ^ (1 / (Module.finrank ℚ K : ℝ)) := by
-- proof
  rw [FinitePlace.normalizedAbsoluteValue, AbsoluteValue.rpow_apply, FinitePlace.coe_apply]

end NumberField

namespace NumberField

/--
[FinitePlace.normalizedAbsoluteValue_apply_eq_adicAbv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/NormalizedPlace.lean)
-/
@[path]
lemma FinitePlace.normalizedAbsoluteValue_apply_eq_adicAbv
  [Field K] [NumberField K]
  {v : FinitePlace K}
  {x : K} :
-- imply
  v.normalizedAbsoluteValue x =
    (HeightOneSpectrum.adicAbv K v.maximalIdeal x) ^
    (1 / (Module.finrank ℚ K : ℝ)) := by
-- proof
  rw [FinitePlace.normalizedAbsoluteValue_apply,
    ← FinitePlace.norm_embedding v.maximalIdeal x, FinitePlace.norm_embedding_eq]

end NumberField

namespace NumberField

/--
[InfinitePlace.normalizedAbsoluteValue_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/NormalizedPlace.lean)
-/
@[path]
lemma InfinitePlace.normalizedAbsoluteValue_apply
  [Field K] [NumberField K]
  {v : InfinitePlace K}
  {x : K} :
-- imply
  v.normalizedAbsoluteValue x = v x ^ ((v.mult : ℝ) / (Module.finrank ℚ K : ℝ)) := by
-- proof
  rw [InfinitePlace.normalizedAbsoluteValue, AbsoluteValue.rpow_apply, InfinitePlace.coe_apply]

end NumberField

namespace NumberField

/--
[InfinitePlace.normalizedAbsoluteValue_apply_of_isReal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/NormalizedPlace.lean)
-/
@[path]
lemma InfinitePlace.normalizedAbsoluteValue_apply_of_isReal
  [Field K] [NumberField K]
  {v : InfinitePlace K}
  {x : K}
-- given
  (hv : v.IsReal) :
-- imply
  v.normalizedAbsoluteValue x = v x ^ (1 / (Module.finrank ℚ K : ℝ)) := by
-- proof
  simp [hv.mult_eq_one]

end NumberField

namespace NumberField

/--
[InfinitePlace.normalizedAbsoluteValue_apply_of_isComplex](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/NormalizedPlace.lean)
-/
@[path]
lemma InfinitePlace.normalizedAbsoluteValue_apply_of_isComplex
  [Field K] [NumberField K]
  {v : InfinitePlace K}
  {x : K}
-- given
  (hv : v.IsComplex) :
-- imply
  v.normalizedAbsoluteValue x = v x ^ (2 / (Module.finrank ℚ K : ℝ)) := by
-- proof
  simp [hv.mult_eq_two]

end NumberField


-- created on 2026-10-20
-- updated on 2026-10-26
