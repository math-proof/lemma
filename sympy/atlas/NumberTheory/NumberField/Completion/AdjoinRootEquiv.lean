/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/AdjoinRootEquiv.lean -/

import sympy.atlas.NumberTheory.NumberField.Completion.FiniteLiesOverDegreeBound
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.AdjoinRoot

/-!
# Completion equivalence from an explicit local root

For a number-field extension `L / K` and finite places `v` of `K` and `w`
of `L` with `w` lying over `v`, an explicit root in the completion
`w.adicCompletion L` of an irreducible local polynomial of matching degree
identifies the completion with the corresponding adjoin-root algebra.

## Primary source and ATLAS source map

The mathematical source is MIT 18.785, *Number Theory I*, Lecture 11,
Theorem 11.20, pages 6--7:
<https://ocw.mit.edu/courses/18-785-number-theory-i-fall-2021/mit18_785f21_lec11.pdf>.
In its nonarchimedean proof, a polynomial `g` is chosen, the global extension
is realized as `K[X] / (g)`, and its completion is identified with the local
algebra `K̂[X] / (g)`.  The theorem below is a documented abstraction of that
final identification step: it takes local irreducibility, equality with the
global degree, and a local root as explicit hypotheses rather than constructing
them.

This module is a bounded stage of ATLAS `NumberTheoryI` item N234,
Theorem 11.20. It maps specifically to
`adicCompletion_algEquiv_adjoinRoot_of_adjoinRoot` at
`v1/Atlas/NumberTheoryI/code/LocalGlobal.lean` lines 468--515:
<https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean#L418-L515>
Lines 418--466 are admitted inputs and this theorem takes the local root
explicitly, so root transport remains a later stage.
-/

namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField NumberField.LiesOver

theorem adicCompletion_algEquiv_adjoinRoot_of_root
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal]
    (g : Polynomial K)
    (hg : Irreducible (g.map (algebraMap K (v.adicCompletion K))))
    (hdeg : Module.finrank K L = g.natDegree)
    (x : w.adicCompletion L)
    (hx : Polynomial.aeval x
      (g.map (algebraMap K (v.adicCompletion K))) = 0) :
    Nonempty (w.adicCompletion L ≃ₐ[v.adicCompletion K]
      AdjoinRoot (g.map (algebraMap K (v.adicCompletion K)))) := by
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
