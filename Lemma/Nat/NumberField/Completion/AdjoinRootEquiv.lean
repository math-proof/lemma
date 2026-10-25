import Mathlib
import sympy.Basic
import Theorem.NumberTheory.NumberField.Completion.FiniteLiesOverDegreeBound
import Lemma.Nat.NumberField.Completion.FiniteLiesOverDegreeBound
open scoped NumberField NumberField.LiesOver


namespace IsDedekindDomain.HeightOneSpectrum

/--
[adicCompletion_algEquiv_adjoinRoot_of_root](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/AdjoinRootEquiv.lean)
-/
@[path]
lemma adicCompletion_algEquiv_adjoinRoot_of_root
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
  let g_v := g.map (algebraMap K (v.adicCompletion K))
  let _ : Fact (Irreducible g_v) := ⟨hg⟩
  let _ : FiniteDimensional (v.adicCompletion K) (AdjoinRoot g_v) :=
    (AdjoinRoot.powerBasis hg.ne_zero).finite
  let phi : AdjoinRoot g_v →ₐ[v.adicCompletion K] w.adicCompletion L :=
    AdjoinRoot.liftAlgHom g_v (Algebra.ofId _ _) x
      (by simpa [Polynomial.aeval_def] using hx)
  have hphi_injective : Function.Injective phi := phi.toRingHom.injective
  have hsource : Module.finrank (v.adicCompletion K) (AdjoinRoot g_v) =
    g.natDegree := by
    rw [(AdjoinRoot.powerBasis hg.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim]
    exact Polynomial.natDegree_map (algebraMap K (v.adicCompletion K))
  have htarget : Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
    g.natDegree := by
    apply Nat.le_antisymm
    · exact (finrank_adicCompletion_le v w).trans_eq hdeg
    · rw [← hsource]
      exact LinearMap.finrank_le_finrank_of_injective
        (f := phi.toLinearMap) hphi_injective
  have hphi_surjective : Function.Surjective phi :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hsource.trans htarget.symm) (f := phi.toLinearMap)).mp hphi_injective
  exact ⟨(AlgEquiv.ofBijective phi ⟨hphi_injective, hphi_surjective⟩).symm⟩

end IsDedekindDomain.HeightOneSpectrum


-- created on 2026-10-20
-- updated on 2026-10-23
