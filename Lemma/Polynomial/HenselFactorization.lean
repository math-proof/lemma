import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.HenselFactorization
open Polynomial


/--
[exists_monic_coprime_factorization_of_isAdicComplete](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HenselFactorization.lean)
-/
@[path]
private lemma exists_monic_coprime_factorization_of_isAdicComplete_eq
  [CommRing A]
  {I : Ideal A} [IsAdicComplete I A]
  {f : A[X]}
  {g_bar h_bar : (A ⧸ I)[X]}
-- given
  (hf : f.Monic)
  (hg : g_bar.Monic)
  (hh : h_bar.Monic)
  (hfac : f.map (Ideal.Quotient.mk I) = g_bar * h_bar)
  (hcop : IsCoprime g_bar h_bar) :
-- imply
  ∃ g h : A[X], g.Monic ∧ h.Monic ∧ f = g * h ∧
    g.map (Ideal.Quotient.mk I) = g_bar ∧
    h.map (Ideal.Quotient.mk I) = h_bar := by
-- proof
  apply Polynomial.exists_monic_coprime_factorization_of_isAdicComplete I f hf g_bar h_bar hg hh hfac hcop

/--
[exists_monic_coprime_factorization_of_isAdicComplete_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HenselFactorization.lean)
-/
@[path]
private lemma exists_monic_coprime_factorization_of_isAdicComplete_natDegree_eq
  [CommRing A]
  {I : Ideal A} [IsAdicComplete I A] [Nontrivial (A ⧸ I)]
  {f : A[X]}
  {g_bar h_bar : (A ⧸ I)[X]}
-- given
  (hf : f.Monic)
  (hg : g_bar.Monic)
  (hh : h_bar.Monic)
  (hfac : f.map (Ideal.Quotient.mk I) = g_bar * h_bar)
  (hcop : IsCoprime g_bar h_bar) :
-- imply
  ∃ g h : A[X], g.Monic ∧ h.Monic ∧ f = g * h ∧
    g.map (Ideal.Quotient.mk I) = g_bar ∧
    h.map (Ideal.Quotient.mk I) = h_bar ∧
    g.natDegree = g_bar.natDegree ∧ h.natDegree = h_bar.natDegree := by
-- proof
  apply Polynomial.exists_monic_coprime_factorization_of_isAdicComplete_natDegree I f hf g_bar h_bar hg hh hfac hcop


-- created on 2026-10-20
