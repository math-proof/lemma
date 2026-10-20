/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/GlobalAdjoinRootCompletionEquiv.lean -/

import sympy.atlas.NumberTheory.NumberField.Completion.AdjoinRootEquivOfGlobalEquiv
/-!
# Compositional completion identification from a global adjoin-root equivalence

This is the compositional adapter corresponding to ATLAS `NumberTheoryI` item
N234 / Theorem 11.20, specifically `LocalGlobal.lean` lines 517--548:
<https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean#L517-L548>

Completion identification is supplied by the preceding modules and this theorem
only composes equivalences; it does not construct `L`, `w`, `eL`, the
polynomial, or the approximation/Krasner data.

## ATLAS source-to-API map

ATLAS's supplied `M ≃ AdjoinRoot(g_v)` and the preceding completion equivalence
map to `completion_algEquiv_of_adjoinRoot_globalEquiv`, which composes them as
`eM.trans eW.symm`. This is a **partial stage** of N234, not the full target.
-/

namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField NumberField.LiesOver

theorem completion_algEquiv_of_adjoinRoot_globalEquiv
    {K L M : Type*} [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal]
    [Algebra (v.adicCompletion K) M]
    (g : Polynomial K)
    (hg : Irreducible (g.map (algebraMap K (v.adicCompletion K))))
    (eL : L ≃ₐ[K] AdjoinRoot g)
    (hM : Nonempty (M ≃ₐ[v.adicCompletion K]
      AdjoinRoot (g.map (algebraMap K (v.adicCompletion K))))) :
    Nonempty (M ≃ₐ[v.adicCompletion K] w.adicCompletion L) := by
  obtain ⟨eM⟩ := hM
  obtain ⟨eW⟩ :=
    adicCompletion_algEquiv_adjoinRoot_of_globalEquiv v w g hg eL
  exact ⟨eM.trans eW.symm⟩

end IsDedekindDomain.HeightOneSpectrum
