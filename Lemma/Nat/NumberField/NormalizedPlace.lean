import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.NormalizedPlace
open NumberField


/--
[FinitePlace.normalizedAbsoluteValue_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/NormalizedPlace.lean)
-/
@[path]
private lemma FinitePlace_normalizedAbsoluteValue_apply_eq
  [Field K] [NumberField K]
  {v : FinitePlace K}
  {x : K} :
-- imply
  v.normalizedAbsoluteValue x = v x ^ (1 / (Module.finrank ℚ K : ℝ)) := by
-- proof
  apply NumberField.FinitePlace.normalizedAbsoluteValue_apply v x

/--
[FinitePlace.normalizedAbsoluteValue_apply_eq_adicAbv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/NormalizedPlace.lean)
-/
@[path]
private lemma FinitePlace_normalizedAbsoluteValue_apply_eq_adicAbv_eq
  [Field K] [NumberField K]
  {v : FinitePlace K}
  {x : K} :
-- imply
  v.normalizedAbsoluteValue x =
    (HeightOneSpectrum.adicAbv K v.maximalIdeal x) ^
    (1 / (Module.finrank ℚ K : ℝ)) := by
-- proof
  apply NumberField.FinitePlace.normalizedAbsoluteValue_apply_eq_adicAbv v x

/--
[InfinitePlace.normalizedAbsoluteValue_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/NormalizedPlace.lean)
-/
@[path]
private lemma InfinitePlace_normalizedAbsoluteValue_apply_eq
  [Field K] [NumberField K]
  {v : InfinitePlace K}
  {x : K} :
-- imply
  v.normalizedAbsoluteValue x = v x ^ ((v.mult : ℝ) / (Module.finrank ℚ K : ℝ)) := by
-- proof
  apply NumberField.InfinitePlace.normalizedAbsoluteValue_apply v x

/--
[InfinitePlace.normalizedAbsoluteValue_apply_of_isReal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/NormalizedPlace.lean)
-/
@[path]
private lemma InfinitePlace_normalizedAbsoluteValue_apply_of_isReal_eq
  [Field K] [NumberField K]
  {v : InfinitePlace K}
  {x : K}
-- given
  (hv : v.IsReal) :
-- imply
  v.normalizedAbsoluteValue x = v x ^ (1 / (Module.finrank ℚ K : ℝ)) := by
-- proof
  apply NumberField.InfinitePlace.normalizedAbsoluteValue_apply_of_isReal v hv x

/--
[InfinitePlace.normalizedAbsoluteValue_apply_of_isComplex](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/NormalizedPlace.lean)
-/
@[path]
private lemma InfinitePlace_normalizedAbsoluteValue_apply_of_isComplex_eq
  [Field K] [NumberField K]
  {v : InfinitePlace K}
  {x : K}
-- given
  (hv : v.IsComplex) :
-- imply
  v.normalizedAbsoluteValue x = v x ^ (2 / (Module.finrank ℚ K : ℝ)) := by
-- proof
  apply NumberField.InfinitePlace.normalizedAbsoluteValue_apply_of_isComplex v hv x


-- created on 2026-10-20
