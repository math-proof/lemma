/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/Completion/GlobalAdjoinRootCompletionEquiv.lean -/


import Lemma.Nat.NumberField.Completion.GlobalAdjoinRootCompletionEquiv
/-!
# Tests for the compositional completion identification

Generic checks consuming `completion_algEquiv_of_adjoinRoot_globalEquiv`:
one direct API application and one destructing the `Nonempty` result to
obtain/use the equivalence. These tests exercise the public statement only
and do not duplicate its proof.
-/


namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField NumberField.LiesOver

variable {K L M : Type*} [Field K] [Field L] [Field M]
  [NumberField K] [NumberField L] [Algebra K L]

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

variable [Algebra (v.adicCompletion K) M]

example (g : Polynomial K)
    (hg : Irreducible (g.map (algebraMap K (v.adicCompletion K))))
    (eL : L ≃ₐ[K] AdjoinRoot g)
    (hM : Nonempty (M ≃ₐ[v.adicCompletion K]
      AdjoinRoot (g.map (algebraMap K (v.adicCompletion K))))) :
    Nonempty (M ≃ₐ[v.adicCompletion K] w.adicCompletion L) :=
  completion_algEquiv_of_adjoinRoot_globalEquiv v w g hg eL hM

example (g : Polynomial K)
    (hg : Irreducible (g.map (algebraMap K (v.adicCompletion K))))
    (eL : L ≃ₐ[K] AdjoinRoot g)
    (hM : Nonempty (M ≃ₐ[v.adicCompletion K]
      AdjoinRoot (g.map (algebraMap K (v.adicCompletion K)))))
    (m : M) :
    ∃ _ : w.adicCompletion L, True := by
  obtain ⟨f⟩ :=
    completion_algEquiv_of_adjoinRoot_globalEquiv v w g hg eL hM
  exact ⟨f m, trivial⟩

end IsDedekindDomain.HeightOneSpectrum
