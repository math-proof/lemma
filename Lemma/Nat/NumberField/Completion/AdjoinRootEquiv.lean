import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.Completion.AdjoinRootEquiv
open scoped NumberField NumberField.LiesOver
open IsDedekindDomain.HeightOneSpectrum


/--
[adicCompletion_algEquiv_adjoinRoot_of_root](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/AdjoinRootEquiv.lean)
-/
@[path]
private lemma adicCompletion_algEquiv_adjoinRoot_of_root_eq
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)} [w.asIdeal.LiesOver v.asIdeal]
  {g : Polynomial K}
  {x : w.adicCompletion L}
-- given
  (hg : Irreducible (g.map (algebraMap K (v.adicCompletion K))))
  (hdeg : Module.finrank K L = g.natDegree)
  (hx : Polynomial.aeval x (g.map (algebraMap K (v.adicCompletion K))) = 0) :
-- imply
  Nonempty (w.adicCompletion L ≃ₐ[v.adicCompletion K]
    AdjoinRoot (g.map (algebraMap K (v.adicCompletion K)))) := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.adicCompletion_algEquiv_adjoinRoot_of_root v w g hg hdeg x hx


-- created on 2026-10-20
