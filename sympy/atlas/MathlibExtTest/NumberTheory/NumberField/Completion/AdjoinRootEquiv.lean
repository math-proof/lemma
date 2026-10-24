/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/Completion/AdjoinRootEquiv.lean -/


import Lemma.Nat.NumberField.Completion.AdjoinRootEquiv

/-!
# Tests for the completion adjoin-root equivalence from a local root

Generic checks consuming `adicCompletion_algEquiv_adjoinRoot_of_root`: one
direct API application and one destructing the `Nonempty` result to
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
    (hdeg : Module.finrank K L = g.natDegree)
    (x : w.adicCompletion L)
    (hx : Polynomial.aeval x
      (g.map (algebraMap K (v.adicCompletion K))) = 0) :
    Nonempty (w.adicCompletion L ≃ₐ[v.adicCompletion K]
      AdjoinRoot (g.map (algebraMap K (v.adicCompletion K)))) :=
  adicCompletion_algEquiv_adjoinRoot_of_root v w g hg hdeg x hx

example (g : Polynomial K)
    (hg : Irreducible (g.map (algebraMap K (v.adicCompletion K))))
    (hdeg : Module.finrank K L = g.natDegree)
    (x : w.adicCompletion L)
    (hx : Polynomial.aeval x
      (g.map (algebraMap K (v.adicCompletion K))) = 0)
    (y : w.adicCompletion L) :
    ∃ _ : AdjoinRoot (g.map (algebraMap K (v.adicCompletion K))), True := by
  obtain ⟨e⟩ :=
    adicCompletion_algEquiv_adjoinRoot_of_root v w g hg hdeg x hx
  exact ⟨e y, trivial⟩

end IsDedekindDomain.HeightOneSpectrum
