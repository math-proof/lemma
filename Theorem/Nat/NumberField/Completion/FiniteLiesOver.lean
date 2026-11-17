module

public import Mathlib
public import Theorem.NumberTheory.NumberField.Completion.FiniteLiesOver

public section

open scoped NumberField
open IsDedekindDomain.HeightOneSpectrum


namespace IsDedekindDomain.HeightOneSpectrum

/--
[adicCompletionMap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOver.lean)
-/
public theorem adicCompletionMap_injective
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)} [hvw : w.asIdeal.LiesOver v.asIdeal] :
-- imply
  Function.Injective (adicCompletionMap v w) :=
-- proof
  RingHom.injective _

/--
[adicCompletionMap_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOver.lean)
-/
public theorem adicCompletionMap_algebraMap_eq
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)} [hvw : w.asIdeal.LiesOver v.asIdeal]
  {x : K} :
-- imply
  adicCompletionMap v w (algebraMap K (v.adicCompletion K) x) =
    algebraMap K (w.adicCompletion L) x := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.adicCompletionMap_algebraMap v w x

/--
[continuous_adicCompletionMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOver.lean)
-/
public theorem continuous_adicCompletionMap_eq
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)} [hvw : w.asIdeal.LiesOver v.asIdeal] :
-- imply
  Continuous (adicCompletionMap v w) := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.continuous_adicCompletionMap v w

end IsDedekindDomain.HeightOneSpectrum


-- created on 2026-10-20
-- updated on 2026-10-26
