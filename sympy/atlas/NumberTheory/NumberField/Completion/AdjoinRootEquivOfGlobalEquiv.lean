/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/AdjoinRootEquivOfGlobalEquiv.lean -/

import sympy.atlas.NumberTheory.NumberField.Completion.AdjoinRootEquiv
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.AdjoinRoot

/-!
# Completion equivalence from a global adjoin-root equivalence

For a number-field extension `L / K` with a global algebra equivalence
`L ≃ₐ[K] AdjoinRoot g`, transport the global root to the completion
`w.adicCompletion L` and apply the local-root equivalence. The transported
point is a root of the base-changed polynomial, and the global equivalence
supplies the matching degree identity.

## Mathematical source

This is the final root/degree-to-completion-identification step in the
nonarchimedean proof of Andrew Sutherland, MIT 18.785 *Number Theory I*,
Lecture 11, Theorem 11.20, pp. 6--7:
<https://ocw.mit.edu/courses/18-785-number-theory-i-fall-2021/mit18_785f21_lec11.pdf>.
There an irreducible `g ∈ K[x]` is chosen over the completion, the global
extension is represented as `K[x]/(g)`, its degree is identified with
`deg g`, and the completion is identified with the corresponding quotient.
The declaration below isolates that last implication for number fields and
the canonical finite-place completion, conditional on a supplied global
algebra equivalence and irreducibility after base change.

## ATLAS source map

This module is a bounded stage of ATLAS `NumberTheoryI` item N234,
Theorem 11.20. It maps precisely to
`v1/Atlas/NumberTheoryI/code/LocalGlobal.lean` lines 450--515:
<https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean#L450-L515>
Lines 450--466 are the admitted local-root helper, and lines 468--515 are
the completion equivalence. This corollary replaces that combined block once
a global algebra equivalence is supplied, but it does not construct the
global equivalence or the approximating polynomial.
-/

namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField NumberField.LiesOver

theorem adicCompletion_algEquiv_adjoinRoot_of_globalEquiv
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal]
    (g : Polynomial K)
    (hg : Irreducible (g.map (algebraMap K (v.adicCompletion K))))
    (e : L ≃ₐ[K] AdjoinRoot g) :
    Nonempty (w.adicCompletion L ≃ₐ[v.adicCompletion K]
      AdjoinRoot (g.map (algebraMap K (v.adicCompletion K)))) := by
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
