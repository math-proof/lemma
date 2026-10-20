/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HenselFactorization.lean -/

import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.RingTheory.Smooth.AdicCompletion

/-!
# Monic Hensel factor lifting over adically complete rings

Clean-room implementation derived solely from the corrected mathematical
statement of the standard monic Hensel factor-lifting theorem together with
Mathlib's public APIs. No external formalization source was inspected
or copied.

Let `A` be a commutative ring that is `I`-adically complete for an ideal `I`,
and let `f : A[X]` be monic whose reduction modulo `I` factors as a product
of two monic coprime polynomials. Then the factorization lifts to `A`:
there exist monic `g h : A[X]` with `f = g * h` reducing to the given
residue factors. A corollary records the resulting degree equalities.
-/

namespace Polynomial

variable {A : Type*} [CommRing A]

/-- Standard monic Hensel factor lifting, generic in the ideal.

If `A` is `I`-adically complete and a monic polynomial `f` reduces modulo `I`
to a product of monic coprime polynomials, the factorization lifts to `A`.
The proof packages the residue factorization via the universal coprime
factorization ring, lifts its structure map through `I`-adic completeness,
and evaluates the universal factors over `A`. -/
theorem exists_monic_coprime_factorization_of_isAdicComplete
    (I : Ideal A) [IsAdicComplete I A]
    (f : A[X]) (hf : f.Monic)
    (g_bar h_bar : (A ⧸ I)[X])
    (hg : g_bar.Monic) (hh : h_bar.Monic)
    (hfac : f.map (Ideal.Quotient.mk I) = g_bar * h_bar)
    (hcop : IsCoprime g_bar h_bar) :
    ∃ g h : A[X], g.Monic ∧ h.Monic ∧ f = g * h ∧
      g.map (Ideal.Quotient.mk I) = g_bar ∧
      h.map (Ideal.Quotient.mk I) = h_bar := by
  by_cases hnt : Nontrivial (A ⧸ I)
  · -- Nontrivial quotient: lift through the universal coprime ring.
    -- (`hnt` itself serves as the `Nontrivial` instance below.)
    have hdeg : f.natDegree = g_bar.natDegree + h_bar.natDegree := by
      have e1 : (f.map (Ideal.Quotient.mk I)).natDegree = f.natDegree :=
        hf.natDegree_map (Ideal.Quotient.mk I)
      have e2 : (g_bar * h_bar).natDegree =
          g_bar.natDegree + h_bar.natDegree :=
        hg.natDegree_mul hh
      rw [hfac] at e1
      rw [← e1]
      exact e2
    let pf : MonicDegreeEq A f.natDegree := MonicDegreeEq.mk f hf rfl
    let pg : MonicDegreeEq (A ⧸ I) g_bar.natDegree :=
      MonicDegreeEq.mk g_bar hg rfl
    let ph : MonicDegreeEq (A ⧸ I) h_bar.natDegree :=
      MonicDegreeEq.mk h_bar hh rfl
    have halg : algebraMap A (A ⧸ I) = Ideal.Quotient.mk I :=
      Ideal.Quotient.algebraMap_eq I
    have h1 : (pg : (A ⧸ I)[X]) * (ph : (A ⧸ I)[X]) =
        (pf : A[X]).map (algebraMap A (A ⧸ I)) := by
      have c1 : (pg : (A ⧸ I)[X]) = g_bar := rfl
      have c2 : (ph : (A ⧸ I)[X]) = h_bar := rfl
      have c3 : (pf : A[X]) = f := rfl
      rw [c1, c2, c3, halg]
      exact hfac.symm
    have h2 : IsCoprime (pg : (A ⧸ I)[X]) (ph : (A ⧸ I)[X]) := by
      have c1 : (pg : (A ⧸ I)[X]) = g_bar := rfl
      have c2 : (ph : (A ⧸ I)[X]) = h_bar := rfl
      rw [c1, c2]
      exact hcop
    obtain ⟨ψ, hψ⟩ :=
      Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (I := I)
        ((UniversalCoprimeFactorizationRing.homEquiv (A ⧸ I)
          g_bar.natDegree h_bar.natDegree hdeg pf).symm ⟨(pg, ph), h1, h2⟩)
    set E := UniversalCoprimeFactorizationRing.homEquiv A
      g_bar.natDegree h_bar.natDegree hdeg pf ψ with hE
    have hgh := E.2
    have nat1 := UniversalCoprimeFactorizationRing.homEquiv_comp_fst A
      g_bar.natDegree h_bar.natDegree hdeg pf ψ (Ideal.Quotient.mkₐ A I)
    have nat2 := UniversalCoprimeFactorizationRing.homEquiv_comp_snd A
      g_bar.natDegree h_bar.natDegree hdeg pf ψ (Ideal.Quotient.mkₐ A I)
    rw [← hE] at nat1 nat2
    refine ⟨(E.1.1 : A[X]), (E.1.2 : A[X]), E.1.1.monic, E.1.2.monic, ?_,
      ?_, ?_⟩
    · have hprod : (E.1.1 : A[X]) * (E.1.2 : A[X]) =
          (pf : A[X]).map (algebraMap A A) := hgh.1
      have hmap : (pf : A[X]).map (algebraMap A A) = f := by
        have c : (pf : A[X]) = f := rfl
        rw [c, Algebra.algebraMap_self, Polynomial.map_id]
      rw [hprod]
      exact hmap.symm
    · have cg : (pg : (A ⧸ I)[X]) = g_bar := rfl
      have e1 : ((UniversalCoprimeFactorizationRing.homEquiv (A ⧸ I)
            g_bar.natDegree h_bar.natDegree hdeg pf
            ((Ideal.Quotient.mkₐ A I).comp ψ)).1.1 : (A ⧸ I)[X]) = g_bar := by
        rw [hψ, Equiv.apply_symm_apply]
        exact cg
      have nat1c := congrArg
        (fun x : MonicDegreeEq (A ⧸ I) g_bar.natDegree => (x : (A ⧸ I)[X]))
        nat1
      simp only [MonicDegreeEq.map_coe, ← AlgHom.toRingHom_eq_coe,
        Ideal.Quotient.mkₐ_toRingHom] at nat1c
      have red1 : (E.1.1 : A[X]).map (Ideal.Quotient.mk I) = g_bar := by
        rw [e1] at nat1c
        exact nat1c.symm
      exact red1
    · have ch : (ph : (A ⧸ I)[X]) = h_bar := rfl
      have e2 : ((UniversalCoprimeFactorizationRing.homEquiv (A ⧸ I)
            g_bar.natDegree h_bar.natDegree hdeg pf
            ((Ideal.Quotient.mkₐ A I).comp ψ)).1.2 : (A ⧸ I)[X]) = h_bar := by
        rw [hψ, Equiv.apply_symm_apply]
        exact ch
      have nat2c := congrArg
        (fun x : MonicDegreeEq (A ⧸ I) h_bar.natDegree => (x : (A ⧸ I)[X]))
        nat2
      simp only [MonicDegreeEq.map_coe, ← AlgHom.toRingHom_eq_coe,
        Ideal.Quotient.mkₐ_toRingHom] at nat2c
      have red2 : (E.1.2 : A[X]).map (Ideal.Quotient.mk I) = h_bar := by
        rw [e2] at nat2c
        exact nat2c.symm
      exact red2
  · -- Trivial quotient: every reduction equality holds vacuously.
    have : Subsingleton (A ⧸ I) := not_nontrivial_iff_subsingleton.mp hnt
    exact ⟨f, 1, hf, monic_one, by simp, Subsingleton.elim _ _,
      Subsingleton.elim _ _⟩

/-- Degree corollary of monic Hensel factor lifting.

The lifted factors have the same degrees as the residue factors. The
`Nontrivial (A ⧸ I)` hypothesis is sharp: over the trivial quotient every
reduction equality is vacuous, so no degree conclusion can hold there. -/
theorem exists_monic_coprime_factorization_of_isAdicComplete_natDegree
    (I : Ideal A) [IsAdicComplete I A] [Nontrivial (A ⧸ I)]
    (f : A[X]) (hf : f.Monic)
    (g_bar h_bar : (A ⧸ I)[X])
    (hg : g_bar.Monic) (hh : h_bar.Monic)
    (hfac : f.map (Ideal.Quotient.mk I) = g_bar * h_bar)
    (hcop : IsCoprime g_bar h_bar) :
    ∃ g h : A[X], g.Monic ∧ h.Monic ∧ f = g * h ∧
      g.map (Ideal.Quotient.mk I) = g_bar ∧
      h.map (Ideal.Quotient.mk I) = h_bar ∧
      g.natDegree = g_bar.natDegree ∧ h.natDegree = h_bar.natDegree := by
  obtain ⟨g, h, hgM, hhM, hgh, hr1, hr2⟩ :=
    exists_monic_coprime_factorization_of_isAdicComplete I f hf g_bar h_bar
      hg hh hfac hcop
  have e1 : (g.map (Ideal.Quotient.mk I)).natDegree = g.natDegree :=
    hgM.natDegree_map (Ideal.Quotient.mk I)
  have e2 : (h.map (Ideal.Quotient.mk I)).natDegree = h.natDegree :=
    hhM.natDegree_map (Ideal.Quotient.mk I)
  rw [hr1] at e1
  rw [hr2] at e2
  exact ⟨g, h, hgM, hhM, hgh, hr1, hr2, e1.symm, e2.symm⟩

end Polynomial
