/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/Completion/AdjoinRootEquivOfGlobalEquiv.lean -/


import Lemma.Nat.NumberField.Completion.AdjoinRootEquivOfGlobalEquiv

/-!
# Tests for the completion equivalence from a global equivalence

Generic checks consuming `adicCompletion_algEquiv_adjoinRoot_of_globalEquiv`:
one direct API application and one destructing the `Nonempty` result to
obtain/use the equivalence. These tests exercise the public statement only
and do not duplicate its proof.
-/


namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField NumberField.LiesOver

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

example (g : Polynomial K)
    (hg : Irreducible (g.map (algebraMap K (v.adicCompletion K))))
    (e : L ≃ₐ[K] AdjoinRoot g) :
    Nonempty (w.adicCompletion L ≃ₐ[v.adicCompletion K]
      AdjoinRoot (g.map (algebraMap K (v.adicCompletion K)))) :=
  adicCompletion_algEquiv_adjoinRoot_of_globalEquiv v w g hg e

example (g : Polynomial K)
    (hg : Irreducible (g.map (algebraMap K (v.adicCompletion K))))
    (e : L ≃ₐ[K] AdjoinRoot g)
    (y : w.adicCompletion L) :
    ∃ _ : AdjoinRoot (g.map (algebraMap K (v.adicCompletion K))), True := by
  obtain ⟨f⟩ :=
    adicCompletion_algEquiv_adjoinRoot_of_globalEquiv v w g hg e
  exact ⟨f y, trivial⟩

end IsDedekindDomain.HeightOneSpectrum
