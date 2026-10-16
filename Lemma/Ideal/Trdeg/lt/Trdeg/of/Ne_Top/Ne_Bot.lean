import Mathlib
import sympy.Basic
open Cardinal Polynomial


private lemma algebraicIndependent_option_elim
  {K : Type u} {R : Type v} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
  (I : Ideal R) {y : ι → R} {a : R}
-- given
  (hy : AlgebraicIndependent K (Ideal.Quotient.mk I ∘ y))
  (haI : a ∈ I)
  (ha : a ≠ 0) :
-- imply
  AlgebraicIndependent K (fun o : Option ι => o.elim a y) := by
-- proof
  have hy' : AlgebraicIndependent K y := hy.of_comp (Ideal.Quotient.mkₐ K I)
  rw [hy'.option_iff_transcendental]
  have hinj : ∀ b : Algebra.adjoin K (Set.range y), (b : R) ∈ I → b = 0 := by
    rintro ⟨b, hb⟩ hbI
    obtain ⟨P, hPb⟩ : ∃ P : MvPolynomial ι K, MvPolynomial.aeval y P = b := by
      have hb' := hb
      rwa [Algebra.adjoin_range_eq_range_aeval] at hb'
    have h0 : MvPolynomial.aeval (Ideal.Quotient.mk I ∘ y) P = 0 := by
      change MvPolynomial.aeval (fun i => Ideal.Quotient.mkₐ K I (y i)) P = 0
      rwa [← MvPolynomial.comp_aeval (f := y) (φ := Ideal.Quotient.mkₐ K I), AlgHom.comp_apply,
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, hPb]
    have hP : P = 0 := hy (by rw [h0, map_zero])
    refine Subtype.ext (show b = 0 by rw [← hPb, hP, map_zero])
  rintro ⟨q, hq0, hqa⟩
  obtain ⟨q', hq, hndvd⟩ := q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hq0 0
  rw [map_zero, sub_zero] at hq hndvd
  have hq'a : aeval a q' = 0 := by
    rw [hq, map_mul, map_pow, aeval_X] at hqa
    exact (mul_eq_zero.mp hqa).resolve_left (pow_ne_zero _ ha)
  have hc : algebraMap (Algebra.adjoin K (Set.range y)) R (q'.coeff 0) = -(a * aeval a q'.divX) := by
    have := congrArg (aeval a) q'.X_mul_divX_add
    rwa [map_add, map_mul, aeval_X, aeval_C, hq'a, ← eq_sub_iff_add_eq', zero_sub] at this
  have hcI : ((q'.coeff 0 : Algebra.adjoin K (Set.range y)) : R) ∈ I := by
    rw [show ((q'.coeff 0 : Algebra.adjoin K (Set.range y)) : R) =
      algebraMap (Algebra.adjoin K (Set.range y)) R (q'.coeff 0) from rfl, hc]
    exact I.neg_mem (I.mul_mem_right _ haI)
  refine hndvd (X_dvd_iff.mpr (hinj _ hcI))


/--
[Algebra_trdeg_quotient_lt](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_trdeg_quotient_lt.lean)
-/
@[path]
private lemma main
  {K : Type u} {R : Type v} [Field K] [CommRing R] [IsDomain R] [Algebra K R] [Algebra.FiniteType K R]
  {I : Ideal R}
-- given
  (hI : I ≠ ⊥)
  (hI' : I ≠ ⊤) :
-- imply
  Algebra.trdeg K (R ⧸ I) < Algebra.trdeg K R := by
-- proof
  obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp (trdeg_lt_aleph0_of_finiteType (R := K) (S := R))
  have key : ∀ t : Subtype fun s : Set (R ⧸ I) => AlgebraicIndepOn K _root_.id s,
      #t.1 + 1 ≤ (n : Cardinal) := by
    rintro ⟨t, ht⟩
    choose y hy using fun i : t => Ideal.Quotient.mk_surjective (I := I) i.1
    have hty : Ideal.Quotient.mk I ∘ y = fun i : t => (i.1 : R ⧸ I) := funext hy
    change AlgebraicIndependent K (fun i : t => (i.1 : R ⧸ I)) at ht
    rw [← hty] at ht
    have hind := algebraicIndependent_option_elim I ht haI ha
    simpa [Cardinal.mk_option, hn] using hind.cardinalMk_le_trdeg
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI'
  have hempty : AlgebraicIndepOn K _root_.id (∅ : Set (R ⧸ I)) :=
    (algebraicIndependent_empty_iff K (R ⧸ I)).mpr (algebraMap K (R ⧸ I)).injective
  have : Nonempty (Subtype fun s : Set (R ⧸ I) => AlgebraicIndepOn K _root_.id s) := ⟨⟨∅, hempty⟩⟩
  have hn1 : 1 ≤ n := by
    have := key ⟨∅, hempty⟩
    rwa [Cardinal.mk_eq_zero, zero_add, ← Nat.cast_one, Nat.cast_le] at this
  rw [hn, Algebra.trdeg]
  refine (ciSup_le fun t => ?_).trans_lt (Nat.cast_lt.mpr (Nat.sub_one_lt_of_lt hn1) :
    ((n - 1 : ℕ) : Cardinal) < n)
  have h := key t
  have hfin : #t.1 < ℵ₀ := lt_of_le_of_lt (self_le_add_right _ _) (h.trans_lt (natCast_lt_aleph0 (n := n)))
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.mp hfin
  rw [hm] at h ⊢
  norm_cast at h ⊢
  omega


-- created on 2026-10-13
