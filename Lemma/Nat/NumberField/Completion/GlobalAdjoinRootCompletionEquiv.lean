import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.Completion.GlobalAdjoinRootCompletionEquiv
open scoped NumberField NumberField.LiesOver
open IsDedekindDomain.HeightOneSpectrum


/--
[completion_algEquiv_of_adjoinRoot_globalEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/GlobalAdjoinRootCompletionEquiv.lean)
-/
@[path]
private lemma completion_algEquiv_of_adjoinRoot_globalEquiv_eq
  [Field K] [Field L] [Field M] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)} [Algebra (v.adicCompletion K) M]
  {w : HeightOneSpectrum (𝓞 L)} [w.asIdeal.LiesOver v.asIdeal]
  {g : Polynomial K}
-- given
  (hg : Irreducible (g.map (algebraMap K (v.adicCompletion K))))
  (eL : L ≃ₐ[K] AdjoinRoot g)
  (hM : Nonempty (M ≃ₐ[v.adicCompletion K] AdjoinRoot (g.map (algebraMap K (v.adicCompletion K))))) :
-- imply
  Nonempty (M ≃ₐ[v.adicCompletion K] w.adicCompletion L) := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.completion_algEquiv_of_adjoinRoot_globalEquiv v w g hg eL hM


-- created on 2026-10-20
