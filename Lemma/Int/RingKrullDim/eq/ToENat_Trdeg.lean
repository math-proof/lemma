import Mathlib
import sympy.Basic


private lemma exists_ltSeries_comap_eq_last
  [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
-- given
  (hinj : Function.Injective (algebraMap R S))
  (l : LTSeries (PrimeSpectrum R)) :
-- imply
  ∃ L : LTSeries (PrimeSpectrum S), L.length = l.length ∧
    PrimeSpectrum.comap (algebraMap R S) L.last = l.last := by
-- proof
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  induction l using RelSeries.inductionOn' with
  | singleton x =>
    obtain ⟨q, hq⟩ := Algebra.IsIntegral.comap_surjective R S x
    exact ⟨RelSeries.singleton _ q, rfl, hq⟩
  | snoc l x hx ih =>
    obtain ⟨L, hlen, hlast⟩ := ih
    have hle : L.last.asIdeal.comap (algebraMap R S) ≤ x.asIdeal := by
      have h1 : PrimeSpectrum.comap (algebraMap R S) L.last ≤ x := hlast ▸ le_of_lt hx
      refine (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr h1
    obtain ⟨Q, hQge, hQprime, hQcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal L.last.asIdeal hle
    have hlx : l.last < x := hx
    have hQlt : L.last < (⟨Q, hQprime⟩ : PrimeSpectrum S) := by
      refine lt_of_le_of_ne ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hQge) ?_
      intro h
      refine absurd ?_ (ne_of_lt hlx)
      calc
        _ = PrimeSpectrum.comap (algebraMap R S) L.last := hlast.symm
        _ = PrimeSpectrum.comap (algebraMap R S) ⟨Q, hQprime⟩ := by rw [h]
        _ = x := PrimeSpectrum.ext hQcomap
    refine ⟨L.snoc ⟨Q, hQprime⟩ hQlt, by simp [hlen], ?_⟩
    simp only [RelSeries.last_snoc]
    apply PrimeSpectrum.ext hQcomap

private lemma ringKrullDim_eq_of_isIntegral_of_injective
  [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
-- given
  (hinj : Function.Injective (algebraMap R S)) :
-- imply
  ringKrullDim R = ringKrullDim S := by
-- proof
  refine le_antisymm ?_ ?_
  ·
    change Order.krullDim (PrimeSpectrum R) ≤ Order.krullDim (PrimeSpectrum S)
    refine iSup_le fun l => ?_
    obtain ⟨L, hlen, -⟩ := exists_ltSeries_comap_eq_last hinj l
    rw [← hlen]
    apply Order.LTSeries.length_le_krullDim L
  ·
    change Order.krullDim (PrimeSpectrum S) ≤ Order.krullDim (PrimeSpectrum R)
    refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
    intro q1 q2 hlt
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
    obtain ⟨y, hy2, hy1⟩ := SetLike.exists_of_lt ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hlt)
    apply Ideal.under_lt_under_of_integral_mem_sdiff
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hlt.le) ⟨hy2, hy1⟩
      (Algebra.IsIntegral.isIntegral y)

private lemma ringKrullDim_mvPolynomial_fin
  {k : Type u} [Field k] (s : ℕ) :
  ringKrullDim (MvPolynomial (Fin s) k) = s := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    ENat.card_eq_coe_natCard, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_cast

private lemma isTranscendenceBasis_of_injective_of_isIntegral
  {k : Type u} {A : Type v} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
  (s : ℕ) (g : MvPolynomial (Fin s) k →ₐ[k] A)
-- given
  (hinj : Function.Injective g)
  (hint : g.IsIntegral) :
-- imply
  IsTranscendenceBasis k (fun i : Fin s => g (MvPolynomial.X i)) := by
-- proof
  have hind : AlgebraicIndependent k (fun i : Fin s => g (MvPolynomial.X i)) := by
    have hae : MvPolynomial.aeval (fun i : Fin s => g (MvPolynomial.X i)) = g := by
      ext i
      simp
    change Function.Injective (MvPolynomial.aeval (fun i : Fin s => g (MvPolynomial.X i)))
    rw [hae]
    apply hinj
  refine hind.isTranscendenceBasis_iff_isAlgebraic.mpr ?_
  have hrange : Algebra.adjoin k (Set.range fun i : Fin s => g (MvPolynomial.X i)) = g.range := by
    have : (Set.range fun i : Fin s => g (MvPolynomial.X i)) =
        g '' Set.range (MvPolynomial.X : Fin s → MvPolynomial (Fin s) k) := by
      ext a
      simp only [Set.mem_range, Set.mem_image, exists_exists_eq_and]
    rw [this, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top]
  rw [hrange]
  have : Algebra.IsIntegral g.range A := by
    constructor
    intro a
    obtain ⟨p, hp, hpa⟩ := hint a
    refine ⟨p.map (g.rangeRestrict : MvPolynomial (Fin s) k →+* g.range), hp.map _, ?_⟩
    have h1 : (algebraMap g.range A).comp (g.rangeRestrict : MvPolynomial (Fin s) k →+* g.range) =
        (g : MvPolynomial (Fin s) k →+* A) := by
      apply RingHom.ext
      intro x
      rw [RingHom.comp_apply]
      show (Subalgebra.val _) (g.rangeRestrict x) = g x
      rw [← AlgHom.comp_apply, AlgHom.val_comp_rangeRestrict]
    rwa [Polynomial.eval₂_map, h1]
  apply Algebra.IsIntegral.isAlgebraic


/--
[Algebra_ringKrullDim_eq_toENat_trdeg_of_finiteType](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_ringKrullDim_eq_toENat_trdeg_of_finiteType.lean)
-/
@[path]
private lemma main
  {k : Type u} {A : Type v} [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] :
-- imply
  ringKrullDim A = (Cardinal.toENat (Algebra.trdeg k A) : WithBot ENat) := by
-- proof
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  have hdim : ringKrullDim A = s := by
    let _ : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
    have : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨fun a => hint a⟩
    have h := ringKrullDim_eq_of_isIntegral_of_injective (R := MvPolynomial (Fin s) k) (S := A) hinj
    rw [← h, ringKrullDim_mvPolynomial_fin]
  have htr : Algebra.trdeg k A = s := by
    have hB := isTranscendenceBasis_of_injective_of_isIntegral s g hinj hint
    have h1 := hB.lift_cardinalMk_eq_trdeg
    rw [Cardinal.mk_fin, Cardinal.lift_natCast] at h1
    refine Cardinal.lift_injective ?_
    rw [Cardinal.lift_natCast]
    apply h1.symm
  rw [hdim, htr, Cardinal.toENat_nat]
  rfl


-- created on 2026-10-13
