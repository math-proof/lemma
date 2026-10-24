import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.IdeleNorm
open NumberField IsDedekindDomain Ideles Classical in


/--
[extensionEmbedding_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdeleNorm.lean)
-/
@[path]
lemma extensionEmbedding_algebraMap
  [Field K]
  [NumberField K]
  {v : InfinitePlace K}
  {y : K} :
-- imply
  InfinitePlace.Completion.extensionEmbedding v (algebraMap K v.Completion y) = v.embedding y := by
-- proof
  rw [show algebraMap K v.Completion y =
    ((WithAbs.equiv v.1).symm y : v.Completion) from rfl,
    InfinitePlace.Completion.extensionEmbedding_coe, RingEquiv.apply_symm_apply]

/--
[HeightOneSpectrum.localNormHom_mem_integers](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdeleNorm.lean)
-/
@[path]
private lemma localNormHom_mem_integers_eq
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [FiniteDimensional K L]
  {w : HeightOneSpectrum (𝓞 L)}
  {v : HeightOneSpectrum (𝓞 K)}
  {x : w.adicCompletion L}
-- given
  (hw : v.asIdeal ≤ Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal)
  (hx : x ∈ w.adicCompletionIntegers L) :
-- imply
  HeightOneSpectrum.localNormHom w v hw x ∈ v.adicCompletionIntegers K := by
-- proof
  apply HeightOneSpectrum.localNormHom_mem_integers w v hw x hx

/--
[HeightOneSpectrum.finite_placesAbove](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdeleNorm.lean)
-/
@[path]
private lemma finite_placesAbove_eq
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [FiniteDimensional K L]
  {v : HeightOneSpectrum (𝓞 K)} :
-- imply
  Set.Finite ({w : HeightOneSpectrum (𝓞 L) | w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal}) := by
-- proof
  apply HeightOneSpectrum.finite_placesAbove v

/--
[HeightOneSpectrum.liesOver_of_mem_placesAbove](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdeleNorm.lean)
-/
@[path]
private lemma liesOver_of_mem_placesAbove_eq
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [FiniteDimensional K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)}
-- given
  (hw : w ∈ HeightOneSpectrum.placesAbove v (L := L)) :
-- imply
  v.asIdeal ≤ Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal := by
-- proof
  apply HeightOneSpectrum.liesOver_of_mem_placesAbove hw

/--
[finiteNormComponent_mem_integers_almost_all](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdeleNorm.lean)
-/
@[path]
private lemma finiteNormComponent_mem_integers_almost_all_eq
  {K : Type*}
  [Field K]
  [NumberField K]
  {L : Type*}
  [Field L]
  [NumberField L]
  [Algebra K L]
  [FiniteDimensional K L]
  {b : FiniteAdeleRing (𝓞 L) L} :
-- imply
  ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, (finiteNormComponent K L v) b ∈ v.adicCompletionIntegers K := by
-- proof
  apply finiteNormComponent_mem_integers_almost_all K L b


-- created on 2026-10-23
