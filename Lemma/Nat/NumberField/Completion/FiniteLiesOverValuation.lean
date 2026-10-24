import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.Completion.FiniteLiesOverValuation
open scoped NumberField
open WithZeroTopology
open IsDedekindDomain.HeightOneSpectrum


namespace IsDedekindDomain.HeightOneSpectrum

/--
[adicCompletionIntegersMap_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOverValuation.lean)
-/
@[path]
lemma adicCompletionIntegersMap_apply
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)} [w.asIdeal.LiesOver v.asIdeal]
  {x : v.adicCompletionIntegers K} :
-- imply
  ((adicCompletionIntegersMap v w x : w.adicCompletionIntegers L) :
    w.adicCompletion L) = adicCompletionMap v w (x : v.adicCompletion K) :=
-- proof
  rfl

end IsDedekindDomain.HeightOneSpectrum

/--
[valuation_adicCompletionMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOverValuation.lean)
-/
@[path]
private lemma valuation_adicCompletionMap_eq
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)} [w.asIdeal.LiesOver v.asIdeal]
  {x : v.adicCompletion K} :
-- imply
  Valued.v (adicCompletionMap v w x) =
    Valued.v x ^ v.asIdeal.ramificationIdx' w.asIdeal := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.valuation_adicCompletionMap v w x

/--
[adicCompletionMap_mem_integers](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOverValuation.lean)
-/
@[path]
private lemma adicCompletionMap_mem_integers_eq
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)} [w.asIdeal.LiesOver v.asIdeal]
  {x : v.adicCompletion K}
-- given
  (hx : x ∈ v.adicCompletionIntegers K) :
-- imply
  adicCompletionMap v w x ∈ w.adicCompletionIntegers L := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.adicCompletionMap_mem_integers v w x hx


-- created on 2026-10-20
-- updated on 2026-10-23
