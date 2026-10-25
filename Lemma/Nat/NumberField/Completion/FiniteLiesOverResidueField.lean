import Mathlib
import sympy.Basic
import Theorem.NumberTheory.NumberField.Completion.FiniteLiesOverResidueField
open scoped NumberField
open IsDedekindDomain.HeightOneSpectrum


namespace IsDedekindDomain.HeightOneSpectrum

/--
[adicCompletionIntegersMap_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOverResidueField.lean)
-/
@[path]
lemma adicCompletionIntegersMap_algebraMap
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
  apply Subtype.ext
  change adicCompletionMap v w
    (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a)) =
    algebraMap L (w.adicCompletion L)
      (algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) a))
  rw [adicCompletionMap_algebraMap,
    IsScalarTower.algebraMap_apply K L (w.adicCompletion L)]
  congr 1

end IsDedekindDomain.HeightOneSpectrum


-- created on 2026-10-20
-- updated on 2026-10-23
