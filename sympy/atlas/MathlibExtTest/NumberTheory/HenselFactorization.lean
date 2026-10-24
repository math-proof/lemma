/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/HenselFactorization.lean -/


import Lemma.Polynomial.HenselFactorization

/-!
# Tests for monic Hensel factor lifting

Generic API-use tests: with all hypotheses assumed, apply the
factor-lifting theorem and its degree corollary and reuse every conclusion
component at proof level.
-/

namespace Polynomial

variable {A : Type*} [CommRing A]

/-- The lifted factors recover the residue degree sum over `A`. -/
example (I : Ideal A) [IsAdicComplete I A] [Nontrivial (A ⧸ I)]
    (f : A[X]) (hf : f.Monic)
    (g_bar h_bar : (A ⧸ I)[X])
    (hg : g_bar.Monic) (hh : h_bar.Monic)
    (hfac : f.map (Ideal.Quotient.mk I) = g_bar * h_bar)
    (hcop : IsCoprime g_bar h_bar) :
    f.natDegree = g_bar.natDegree + h_bar.natDegree := by
  obtain ⟨g, h, hgM, hhM, hgh, hr1, hr2⟩ :=
    exists_monic_coprime_factorization_of_isAdicComplete I f hf g_bar h_bar
      hg hh hfac hcop
  have hmul := hgM.natDegree_mul hhM
  rw [← hgh] at hmul
  have e1 : (g.map (Ideal.Quotient.mk I)).natDegree = g.natDegree :=
    hgM.natDegree_map (Ideal.Quotient.mk I)
  have e2 : (h.map (Ideal.Quotient.mk I)).natDegree = h.natDegree :=
    hhM.natDegree_map (Ideal.Quotient.mk I)
  rw [hr1] at e1
  rw [hr2] at e2
  omega

/-- The degree corollary exposes both degree equalities alongside the
factorization. -/
example (I : Ideal A) [IsAdicComplete I A] [Nontrivial (A ⧸ I)]
    (f : A[X]) (hf : f.Monic)
    (g_bar h_bar : (A ⧸ I)[X])
    (hg : g_bar.Monic) (hh : h_bar.Monic)
    (hfac : f.map (Ideal.Quotient.mk I) = g_bar * h_bar)
    (hcop : IsCoprime g_bar h_bar) :
    ∃ g h : A[X], g.Monic ∧ g.natDegree = g_bar.natDegree ∧
      h.Monic ∧ h.natDegree = h_bar.natDegree ∧ f = g * h := by
  obtain ⟨g, h, hgM, hhM, hgh, -, -, r1, r2⟩ :=
    exists_monic_coprime_factorization_of_isAdicComplete_natDegree I f hf
      g_bar h_bar hg hh hfac hcop
  exact ⟨g, h, hgM, r1, hhM, r2, hgh⟩

end Polynomial
