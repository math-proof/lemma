import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped NumberField NumberField.LiesOver


namespace IsDedekindDomain.HeightOneSpectrum

/--
[adicCompletion_algEquiv_adjoinRoot_of_globalEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/AdjoinRootEquivOfGlobalEquiv.lean)
-/
@[path]
lemma adicCompletion_algEquiv_adjoinRoot_of_globalEquiv
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
  let q := g.map (algebraMap K (v.adicCompletion K))
  let x : L := e.symm (AdjoinRoot.root g)
  have hx : Polynomial.aeval x g = 0 := by
    calc
      Polynomial.aeval x g = e.symm (Polynomial.aeval (AdjoinRoot.root g) g) :=
        Polynomial.aeval_algHom_apply e.symm.toAlgHom (AdjoinRoot.root g) g
      _ = 0 := by simp
  have hx_completion :
      Polynomial.aeval (algebraMap L (w.adicCompletion L) x) q = 0 := by
    rw [Polynomial.aeval_map_algebraMap]
    change Polynomial.aeval ((Algebra.algHom K L (w.adicCompletion L)) x) g = 0
    rw [Polynomial.aeval_algHom_apply, hx, map_zero]
  have hdeg : Module.finrank K L = g.natDegree := by
    calc
      Module.finrank K L = Module.finrank K (AdjoinRoot g) :=
        e.toLinearEquiv.finrank_eq
      _ = g.natDegree := finrank_quotient_span_eq_natDegree
  exact adicCompletion_algEquiv_adjoinRoot_of_root v w g hg hdeg
    (algebraMap L (w.adicCompletion L) x) hx_completion

end IsDedekindDomain.HeightOneSpectrum


-- created on 2026-10-20
-- updated on 2026-10-28
