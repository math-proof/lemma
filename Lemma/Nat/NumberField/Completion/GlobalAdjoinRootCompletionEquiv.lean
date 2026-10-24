import Mathlib
import sympy.Basic
open scoped NumberField NumberField.LiesOver


namespace IsDedekindDomain.HeightOneSpectrum

/--
[completion_algEquiv_of_adjoinRoot_globalEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/GlobalAdjoinRootCompletionEquiv.lean)
-/
@[path]
lemma completion_algEquiv_of_adjoinRoot_globalEquiv
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
  obtain ⟨eM⟩ := hM
  obtain ⟨eW⟩ :=
    adicCompletion_algEquiv_adjoinRoot_of_globalEquiv v w g hg eL
  exact ⟨eM.trans eW.symm⟩

end IsDedekindDomain.HeightOneSpectrum


-- created on 2026-10-20
-- updated on 2026-10-23
