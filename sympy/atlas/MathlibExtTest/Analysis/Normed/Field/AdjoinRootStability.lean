/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Normed/Field/AdjoinRootStability.lean -/


import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Lemma.Polynomial.Normed.Field.AdjoinRootStability

/-! # AdjoinRoot stability signature test

Direct signature-level generic example exercising
`Polynomial.exists_pos_adjoinRoot_algEquiv_of_l1Norm_sub_lt`.
-/


open Polynomial
open scoped Polynomial Valued

-- The theorem applies at any complete ultrametric nontrivially normed field;
-- here we only check its signature elaborates generically.
#check @Polynomial.exists_pos_adjoinRoot_algEquiv_of_l1Norm_sub_lt

example (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (f : K[X]) (hf : f.Monic) (hirr : Irreducible f)
    (hsep : f.Separable) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : K[X], g.Monic →
      Polynomial.l1Norm (NormedField.toAbsoluteValue K) (f - g) < δ →
      Nonempty (AdjoinRoot f ≃ₐ[K] AdjoinRoot g) :=
  Polynomial.exists_pos_adjoinRoot_algEquiv_of_l1Norm_sub_lt K f hf hirr hsep

example (K : Type*) [Field K] [NumberField K] (v : NumberField.FinitePlace K)
    (f : (v.maximalIdeal.adicCompletion K)[X]) (hf : f.Monic)
    (hirr : Irreducible f) (hsep : f.Separable) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : (v.maximalIdeal.adicCompletion K)[X], g.Monic →
      Polynomial.l1Norm (NormedField.toAbsoluteValue (v.maximalIdeal.adicCompletion K))
        (f - g) < δ →
      Module.finrank (v.maximalIdeal.adicCompletion K) (AdjoinRoot f) =
        Module.finrank (v.maximalIdeal.adicCompletion K) (AdjoinRoot g) := by
  obtain ⟨δ, hδpos, hstab⟩ :=
    Polynomial.exists_pos_adjoinRoot_algEquiv_of_l1Norm_sub_lt
      (v.maximalIdeal.adicCompletion K) f hf hirr hsep
  exact ⟨δ, hδpos, fun g hg hclose => by
    obtain ⟨e⟩ := hstab g hg hclose
    exact e.toLinearEquiv.finrank_eq⟩
