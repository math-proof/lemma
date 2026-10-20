import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.Completion.FiniteLiesOverInertiaDegree
open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField
open scoped NumberField NumberField.LiesOver


/--
[inertiaDeg_adicCompletionIntegersMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOverInertiaDegree.lean)
-/
@[path]
private lemma inertiaDeg_adicCompletionIntegersMap_eq
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)} [w.asIdeal.LiesOver v.asIdeal] :
-- imply
  (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).inertiaDeg
    (v.adicCompletionIntegers K) =
    w.asIdeal.inertiaDeg (𝓞 K) := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.inertiaDeg_adicCompletionIntegersMap v w


-- created on 2026-10-20
