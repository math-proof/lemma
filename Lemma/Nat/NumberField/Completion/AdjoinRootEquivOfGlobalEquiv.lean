import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.Completion.AdjoinRootEquivOfGlobalEquiv
open scoped NumberField NumberField.LiesOver
open IsDedekindDomain.HeightOneSpectrum


/--
[adicCompletion_algEquiv_adjoinRoot_of_globalEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/AdjoinRootEquivOfGlobalEquiv.lean)
-/
@[path]
private lemma adicCompletion_algEquiv_adjoinRoot_of_globalEquiv_eq
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)} [w.asIdeal.LiesOver v.asIdeal]
  {g : Polynomial K}
-- given
  (hg : Irreducible (g.map (algebraMap K (v.adicCompletion K))))
  (e : L ≃ₐ[K] AdjoinRoot g) :
-- imply
  Nonempty (w.adicCompletion L ≃ₐ[v.adicCompletion K]
    AdjoinRoot (g.map (algebraMap K (v.adicCompletion K)))) := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.adicCompletion_algEquiv_adjoinRoot_of_globalEquiv v w g hg e


-- created on 2026-10-20
