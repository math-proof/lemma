import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.Completion.FiniteLiesOverRamificationIndex
open scoped WithZero NumberField NumberField.LiesOver
open IsDedekindDomain.HeightOneSpectrum


/--
[adicCompletionIntegersMap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOverRamificationIndex.lean)
-/
@[path]
private lemma adicCompletionIntegersMap_injective_eq
  [Field F] [NumberField F] [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 F)}
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)} [w.asIdeal.LiesOver v.asIdeal] :
-- imply
  Function.Injective (adicCompletionIntegersMap v w) := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegersMap_injective v v w

/--
[ramificationIdx_adicCompletionIntegersMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOverRamificationIndex.lean)
-/
@[path]
private lemma ramificationIdx_adicCompletionIntegersMap_eq
  [Field F] [NumberField F] [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 F)}
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)} [w.asIdeal.LiesOver v.asIdeal] :
-- imply
  (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).ramificationIdx
    (v.adicCompletionIntegers K) =
    w.asIdeal.ramificationIdx (𝓞 K) := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.ramificationIdx_adicCompletionIntegersMap v v w


-- created on 2026-10-20
