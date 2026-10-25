/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/Completion/SeparableExtension.lean -/

/-
Author: Muse Code
-/


import Lemma.Nat.NumberField.Completion.SeparableExtension
/-!
# Tests for the finite-place number-field clause of ATLAS Theorem 11.20

Signature-level application of
`IsDedekindDomain.HeightOneSpectrum.separableExtension_isCompletion_finitePlace`:
reproduce the dependent conclusion exactly, then a substantive consumer that
destructures the theorem and returns the same existential field/place data with
both the global/local degree equality and the completion finrank equality.
-/


namespace IsDedekindDomain.HeightOneSpectrum

open IsDedekindDomain

open scoped NumberField NumberField.LiesOver Valued

universe u v

variable {K : Type u} [Field K] [NumberField K]

variable (v : HeightOneSpectrum (𝓞 K))

variable (M : Type v) [Field M] [Algebra (v.adicCompletion K) M]
  [FiniteDimensional (v.adicCompletion K) M]
  [Algebra.IsSeparable (v.adicCompletion K) M]

/-- Direct application: the dependent conclusion itself, reproduced exactly. -/
example :
    ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
      (_ : Algebra.IsSeparable K L) (_ : FiniteDimensional K L)
      (w : HeightOneSpectrum (𝓞 L))
      (hw : w.asIdeal.LiesOver v.asIdeal),
      let _ : w.asIdeal.LiesOver v.asIdeal := hw
      Module.finrank K L =
          Module.finrank (v.adicCompletion K) M ∧
        Nonempty (M ≃ₐ[v.adicCompletion K] w.adicCompletion L) :=
  separableExtension_isCompletion_finitePlace v M

/-- Substantive consumer: return the field/place data with both the
global/local degree equality and the completion finrank equality. -/
example :
    ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
      (_ : Algebra.IsSeparable K L) (_ : FiniteDimensional K L)
      (w : HeightOneSpectrum (𝓞 L))
      (hw : w.asIdeal.LiesOver v.asIdeal),
      let _ : w.asIdeal.LiesOver v.asIdeal := hw
      (Module.finrank K L =
          Module.finrank (v.adicCompletion K) M) ∧
        (Module.finrank (v.adicCompletion K) M =
          Module.finrank (v.adicCompletion K) (w.adicCompletion L)) := by
  obtain ⟨L, hF, hNF, hA, hS, hFD, w, hw, hdeg, ⟨e⟩⟩ :=
    separableExtension_isCompletion_finitePlace (K := K) v M
  let _ : w.asIdeal.LiesOver v.asIdeal := hw
  exact ⟨L, hF, hNF, hA, hS, hFD, w, hw, hdeg, e.toLinearEquiv.finrank_eq⟩

end IsDedekindDomain.HeightOneSpectrum
