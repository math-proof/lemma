import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.Completion.FiniteLiesOverResidueField
open scoped NumberField
open IsDedekindDomain.HeightOneSpectrum


/--
[adicCompletionIntegersMap_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOverResidueField.lean)
-/
@[path]
private lemma adicCompletionIntegersMap_algebraMap_eq
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)} [w.asIdeal.LiesOver v.asIdeal]
  {a : 𝓞 K} :
-- imply
  (adicCompletionIntegersMap v w)
    (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a) =
    algebraMap (𝓞 L) (w.adicCompletionIntegers L)
    (algebraMap (𝓞 K) (𝓞 L) a) := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegersMap_algebraMap v w a


-- created on 2026-10-20
