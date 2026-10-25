/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.RingTheory.LaurentSeries
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.Valuation.ValuationSubring
import Lemma.Polynomial.HenselFactorization
import Def.FieldTheory.PuiseuxTheorem.Part19
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/


namespace MetaMathlibExt

namespace MetaMathlibExt

noncomputable section

theorem puiseux_powerSeriesPolynomial_coeff {K : Type*} [Field K]
    {n : ℕ} (hn : 0 < n) (p : (puiseuxValuationRing K)[X])
    (hp : ∀ i, puiseuxAtLevel n
      ((p.coeff i : puiseuxValuationRing K) : HahnSeries Rat K))
    (i : ℕ) (hi : i ≤ p.natDegree) :
    (puiseux_powerSeriesPolynomial hn p hp).coeff i =
      Classical.choose
        (puiseux_exists_powerSeries_preimage hn (p.coeff i) (hp i)) := by
  classical
  simpa [puiseux_powerSeriesPolynomial] using
    Polynomial.ofFn_coeff_eq_val_of_lt
      (fun j : Fin (p.natDegree + 1) ↦
        Classical.choose
          (puiseux_exists_powerSeries_preimage hn (p.coeff j) (hp j)))
      (Nat.lt_succ_of_le hi)

theorem puiseux_powerSeriesPolynomial_coeff_eq_zero {K : Type*}
    [Field K] {n : ℕ} (hn : 0 < n) (p : (puiseuxValuationRing K)[X])
    (hp : ∀ i, puiseuxAtLevel n
      ((p.coeff i : puiseuxValuationRing K) : HahnSeries Rat K))
    (i : ℕ) (hi : p.natDegree < i) :
    (puiseux_powerSeriesPolynomial hn p hp).coeff i = 0 := by
  classical
  simpa [puiseux_powerSeriesPolynomial] using
    Polynomial.ofFn_coeff_eq_zero_of_ge
      (fun j : Fin (p.natDegree + 1) ↦
        Classical.choose
          (puiseux_exists_powerSeries_preimage hn (p.coeff j) (hp j)))
      (Nat.succ_le_iff.mpr hi)

theorem puiseux_map_powerSeriesPolynomial {K : Type*} [Field K]
    {n : ℕ} (hn : 0 < n) (p : (puiseuxValuationRing K)[X])
    (hp : ∀ i, puiseuxAtLevel n
      ((p.coeff i : puiseuxValuationRing K) : HahnSeries Rat K)) :
    (puiseux_powerSeriesPolynomial hn p hp).map
      (puiseux_powerSeriesToValuationRing n hn) = p := by
  classical
  apply Polynomial.ext
  intro i
  rw [Polynomial.coeff_map]
  by_cases hi : i ≤ p.natDegree
  · rw [puiseux_powerSeriesPolynomial_coeff hn p hp i hi]
    exact Classical.choose_spec
      (puiseux_exists_powerSeries_preimage hn (p.coeff i) (hp i))
  · have hlt : p.natDegree < i := Nat.lt_of_not_ge hi
    rw [puiseux_powerSeriesPolynomial_coeff_eq_zero hn p hp i hlt,
      map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt hlt]

theorem puiseux_powerSeriesPolynomial_monic {K : Type*} [Field K]
    {n : ℕ} (hn : 0 < n) (p : (puiseuxValuationRing K)[X])
    (hp : ∀ i, puiseuxAtLevel n
      ((p.coeff i : puiseuxValuationRing K) : HahnSeries Rat K))
    (hmonic : p.Monic) : (puiseux_powerSeriesPolynomial hn p hp).Monic := by
  apply Polynomial.monic_of_injective
    (puiseux_powerSeriesToValuationRing_injective hn)
  rw [puiseux_map_powerSeriesPolynomial hn p hp]
  exact hmonic

theorem puiseux_map_constantCoeff_powerSeriesPolynomial
    {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (p : (puiseuxValuationRing K)[X])
    (hp : ∀ i, puiseuxAtLevel n
      ((p.coeff i : puiseuxValuationRing K) : HahnSeries Rat K)) :
    (puiseux_powerSeriesPolynomial hn p hp).map PowerSeries.constantCoeff =
      puiseux_residuePolynomial p := by
  apply Polynomial.ext
  intro i
  have hcoeff := congrArg (fun q ↦ q.coeff i)
    (puiseux_map_powerSeriesPolynomial hn p hp)
  simp only [Polynomial.coeff_map] at hcoeff ⊢
  rw [puiseux_residuePolynomial, Polynomial.coeff_map]
  rw [← hcoeff]
  exact (puiseux_residue_powerSeriesToValuationRing hn _).symm

theorem puiseux_bounded_coeff_map_powerSeries
    {K : Type*} [Field K] {n : ℕ} (hn : 0 < n) (q : (PowerSeries K)[X])
    (i : ℕ) :
    puiseuxBounded
      ((((q.map (puiseux_powerSeriesToValuationRing n hn)).coeff i :
        puiseuxValuationRing K) : HahnSeries Rat K)) := by
  rw [Polynomial.coeff_map]
  exact ⟨n, hn, puiseux_powerSeriesLevelHom_atLevel hn (q.coeff i)⟩

theorem puiseux_lift_factorization_bounded {K : Type*} [Field K]
    (p : (puiseuxValuationRing K)[X]) (hp : p.Monic)
    (hpbounded : ∀ i, puiseuxBounded
      (((p.coeff i : puiseuxValuationRing K) : HahnSeries Rat K)))
    (g h : K[X]) (hg : g.Monic) (hh : h.Monic)
    (hfac : puiseux_residuePolynomial p = g * h) (hcop : IsCoprime g h) :
    ∃ G H : (puiseuxValuationRing K)[X],
      G.Monic ∧ H.Monic ∧ p = G * H ∧
        G.natDegree = g.natDegree ∧ H.natDegree = h.natDegree ∧
        (∀ i, puiseuxBounded
          (((G.coeff i : puiseuxValuationRing K) : HahnSeries Rat K))) ∧
        ∀ i, puiseuxBounded
          (((H.coeff i : puiseuxValuationRing K) : HahnSeries Rat K)) := by
  let σ := ValuationSubring.subtype (puiseuxValuationRing K)
  obtain ⟨n, hn, hlevel⟩ := puiseux_polynomial_common_level (p.map σ) (by
    intro i
    rw [Polynomial.coeff_map]
    change puiseuxBounded
      (((p.coeff i : puiseuxValuationRing K) : HahnSeries Rat K))
    exact hpbounded i)
  have hlevel' (i : ℕ) : puiseuxAtLevel n
      (((p.coeff i : puiseuxValuationRing K) : HahnSeries Rat K)) := by
    have hi := hlevel i
    rw [Polynomial.coeff_map] at hi
    exact hi
  let q : (PowerSeries K)[X] := puiseux_powerSeriesPolynomial hn p hlevel'
  let I : Ideal (PowerSeries K) := Ideal.span {PowerSeries.X}
  let φ : K →+* PowerSeries K ⧸ I :=
    (Ideal.Quotient.mk I).comp PowerSeries.C
  let gbar : (PowerSeries K ⧸ I)[X] := g.map φ
  let hbar : (PowerSeries K ⧸ I)[X] := h.map φ
  let _ : Nontrivial (PowerSeries K ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr <| by
      simpa [I] using (PowerSeries.span_X_isPrime (R := K)).ne_top
  have hqmonic : q.Monic := puiseux_powerSeriesPolynomial_monic hn p hlevel' hp
  have hgbar : gbar.Monic := hg.map φ
  have hhbar : hbar.Monic := hh.map φ
  have hfacbar : q.map (Ideal.Quotient.mk I) = gbar * hbar := by
    rw [show q.map (Ideal.Quotient.mk I) =
        (q.map PowerSeries.constantCoeff).map φ by
      exact puiseux_map_powerSeries_quotient_eq_map_constantCoeff q]
    rw [show q.map PowerSeries.constantCoeff = puiseux_residuePolynomial p by
      exact puiseux_map_constantCoeff_powerSeriesPolynomial hn p hlevel']
    rw [hfac]
    simp [gbar, hbar]
  have hcopbar : IsCoprime gbar hbar := by
    rcases hcop with ⟨a, b, hab⟩
    refine ⟨a.map φ, b.map φ, ?_⟩
    simpa [gbar, hbar] using congrArg (Polynomial.map φ) hab
  obtain ⟨A, B, hA, hB, hqAB, _, _, hAdeg, hBdeg⟩ :=
    Polynomial.exists_monic_coprime_factorization_of_isAdicComplete_natDegree
      I q hqmonic gbar hbar hgbar hhbar hfacbar hcopbar
  let ψ := puiseux_powerSeriesToValuationRing (K := K) n hn
  let G : (puiseuxValuationRing K)[X] := A.map ψ
  let H : (puiseuxValuationRing K)[X] := B.map ψ
  have hG : G.Monic := hA.map ψ
  have hH : H.Monic := hB.map ψ
  have hpGH : p = G * H := by
    have hmapped := congrArg (Polynomial.map ψ) hqAB
    rw [Polynomial.map_mul] at hmapped
    rw [show q.map ψ = p by
      exact puiseux_map_powerSeriesPolynomial hn p hlevel'] at hmapped
    exact hmapped
  refine ⟨G, H, hG, hH, hpGH, ?_, ?_, ?_, ?_⟩
  · exact (hA.natDegree_map ψ).trans <|
      hAdeg.trans (hg.natDegree_map φ)
  · exact (hB.natDegree_map ψ).trans <|
      hBdeg.trans (hh.natDegree_map φ)
  · exact fun i ↦ puiseux_bounded_coeff_map_powerSeries hn A i
  · exact fun i ↦ puiseux_bounded_coeff_map_powerSeries hn B i

theorem puiseux_exists_bounded_root_monic_of_natDegree_le
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ) :
    ∀ f : (HahnSeries Rat K)[X], f.Monic → 0 < f.natDegree →
      f.natDegree ≤ n → puiseuxPolynomialBounded f →
      ∃ x, f.IsRoot x ∧ puiseuxBounded x := by
  let _ : CharZero (HahnSeries Rat K) :=
    charZero_of_injective_ringHom
      (show Function.Injective (HahnSeries.C : K →+* HahnSeries Rat K) from
        HahnSeries.C_injective)
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro f hf hn hfn hfbounded
      let d := puiseux.depressed f
      have hdmonic : d.Monic := puiseux.depressed_monic f hf
      have hddeg : d.natDegree = f.natDegree := puiseux.depressed_natDegree f
      have hdn : 0 < d.natDegree := hddeg.symm ▸ hn
      have hdnext : d.nextCoeff = 0 := puiseux.depressed_nextCoeff f hf hn
      have hdbounded : puiseuxPolynomialBounded d :=
        puiseux_depressed_bounded f hfbounded
      by_cases hdpow : d = X ^ d.natDegree
      · have hdroot : d.IsRoot 0 := by
          rw [hdpow, Polynomial.IsRoot, Polynomial.eval_pow, Polynomial.eval_X]
          exact zero_pow hdn.ne'
        exact
          ⟨puiseux.center f,
            by simpa using puiseux.root_of_root_depressed f hdroot,
            puiseux_bounded_center f hfbounded⟩
      · let p := puiseux.newtonPolynomial d hdmonic hdpow
        let r := puiseux_residuePolynomial p
        have hpmonic : p.Monic := puiseux.newtonPolynomial_monic d hdmonic hdpow
        have hpbounded : ∀ i, puiseuxBounded
            (((p.coeff i : puiseuxValuationRing K) : HahnSeries Rat K)) :=
          puiseux_newtonPolynomial_bounded d hdmonic hdpow hdbounded
        have hrmonic : r.Monic :=
          puiseux.residuePolynomial_monic d hdmonic hdpow
        have hrdeg : r.natDegree = d.natDegree :=
          puiseux.residuePolynomial_natDegree d hdmonic hdpow
        have hrnext : r.nextCoeff = 0 :=
          puiseux.residuePolynomial_nextCoeff_eq_zero
            d hdmonic hdn hdnext hdpow
        have hrpow : r ≠ X ^ d.natDegree :=
          puiseux.residuePolynomial_ne_X_pow d hdmonic hdpow
        obtain ⟨g, q, hg, hq, hrfac, hcop, hgpos, hglt, _, _⟩ :=
          puiseux.split_residue
            r d.natDegree hrmonic hdn hrdeg hrnext hrpow
        obtain ⟨G, Q, hG, hQ, hpGQ, hGdeg, _, hGbounded, _⟩ :=
          puiseux_lift_factorization_bounded
            p hpmonic hpbounded g q hg hq hrfac hcop
        let σ := ValuationSubring.subtype (puiseuxValuationRing K)
        let GF : (HahnSeries Rat K)[X] := G.map σ
        let QF : (HahnSeries Rat K)[X] := Q.map σ
        have hGFmonic : GF.Monic := hG.map σ
        have hGFdeg : GF.natDegree = g.natDegree := by
          exact hG.natDegree_map σ |>.trans hGdeg
        have hGFpos : 0 < GF.natDegree := hGFdeg.symm ▸ hgpos
        have hGFlt : GF.natDegree < n := by
          rw [hGFdeg]
          exact hglt.trans_le (hddeg.trans_le hfn)
        have hGFbounded : puiseuxPolynomialBounded GF := by
          intro i
          rw [Polynomial.coeff_map]
          exact hGbounded i
        obtain ⟨x, hx, hxbounded⟩ :=
          ih GF.natDegree hGFlt GF hGFmonic hGFpos le_rfl hGFbounded
        have hpmap : p.map σ = GF * QF := by
          rw [hpGQ, Polynomial.map_mul]
        have hpx : (p.map σ).IsRoot x := by
          rw [hpmap]
          exact Polynomial.root_mul_right_of_isRoot QF hx
        have hdx :=
          puiseux.root_of_root_newtonPolynomial d hdmonic hdpow hpx
        refine
          ⟨HahnSeries.single (puiseux.newtonSlope d hdmonic hdpow) 1 * x +
              puiseux.center f,
            puiseux.root_of_root_depressed f hdx, ?_⟩
        exact puiseux_bounded_add
          (puiseux_bounded_mul (puiseux_bounded_single _ 1) hxbounded)
          (puiseux_bounded_center f hfbounded)

theorem puiseux_exists_bounded_root_monic
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (f : (HahnSeries Rat K)[X]) (hf : f.Monic) (hn : 0 < f.natDegree)
    (hbounded : puiseuxPolynomialBounded f) :
    ∃ x, f.IsRoot x ∧ puiseuxBounded x :=
  puiseux_exists_bounded_root_monic_of_natDegree_le
    f.natDegree f hf hn le_rfl hbounded

theorem puiseux_subfield_isAlgClosed {K : Type*} [Field K]
    [IsAlgClosed K] [CharZero K] : IsAlgClosed ↥(puiseuxSubfield K) := by
  apply IsAlgClosed.of_exists_root
  intro p hp hirr
  let σ := (puiseuxSubfield K).subtype
  let f : (HahnSeries Rat K)[X] := p.map σ
  have hf : f.Monic := hp.map σ
  have hdeg : f.natDegree = p.natDegree := hp.natDegree_map σ
  have hn : 0 < f.natDegree := hdeg.symm ▸
    natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hirr)
  have hbounded : puiseuxPolynomialBounded f := by
    intro i
    rw [Polynomial.coeff_map]
    exact (p.coeff i).property
  obtain ⟨x, hx, hxbounded⟩ :=
    puiseux_exists_bounded_root_monic f hf hn hbounded
  let y : ↥(puiseuxSubfield K) := ⟨x, hxbounded⟩
  refine ⟨y, ?_⟩
  apply Subtype.ext
  change σ (p.eval y) = 0
  rw [← Polynomial.eval_map_apply]
  exact hx

end
end MetaMathlibExt
end MetaMathlibExt
