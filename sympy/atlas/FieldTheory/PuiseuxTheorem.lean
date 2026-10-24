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
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/

namespace MetaMathlibExt

noncomputable section

open Polynomial

private def puiseux_hahnVal (K : Type*) [Field K] :
    Valuation (HahnSeries Rat K) (Multiplicative (WithTop Rat)ᵒᵈ) :=
  AddValuation.toValuation (HahnSeries.addVal Rat K)

private abbrev puiseuxValuationRing (K : Type*) [Field K] :=
  (puiseux_hahnVal K).valuationSubring

private def puiseux_uniformizer {K : Type*} [Field K] (d : Rat) (hd : 0 < d) :
    puiseuxValuationRing K :=
  ⟨HahnSeries.single d 1, by
    rw [show HahnSeries.single d (1 : K) ∈ (puiseux_hahnVal K).valuationSubring ↔
      0 ≤ (HahnSeries.single d (1 : K)).orderTop by
        rw [Valuation.mem_valuationSubring_iff]
        rfl]
    simpa using hd.le⟩

private def puiseux_hahnIdeal {K : Type*} [Field K] (d : Rat) (hd : 0 < d) :
    Ideal (puiseuxValuationRing K) :=
  Ideal.span {puiseux_uniformizer (K := K) d hd}

private def puiseux_constants {K : Type*} [Field K] :
    K →+* puiseuxValuationRing K :=
  (HahnSeries.C (R := K) (Γ := Rat)).codRestrict
    (puiseux_hahnVal K).valuationSubring fun a ↦ by
      rw [show HahnSeries.C a ∈ (puiseux_hahnVal K).valuationSubring ↔
        0 ≤ (HahnSeries.C a : HahnSeries Rat K).orderTop by
          rw [Valuation.mem_valuationSubring_iff]
          rfl]
      by_cases ha : a = 0
      · simp [ha]
      · rw [HahnSeries.C_apply, HahnSeries.orderTop_single ha]
        norm_num

private def puiseux_tail {K : Type*} [Field K] (x : puiseuxValuationRing K) :
    puiseuxValuationRing K :=
  x - puiseux_constants ((x : HahnSeries Rat K).coeff 0)

private noncomputable def puiseux_epsilon {K : Type*} [Field K]
    (x : puiseuxValuationRing K) : Rat := by
  classical
  exact if puiseux_tail x = 0 then 1
    else ((puiseux_tail x : puiseuxValuationRing K) : HahnSeries Rat K).order

private def puiseux_precision {K : Type*} [Field K]
    (p : (puiseuxValuationRing K)[X]) : Rat :=
  let s := insert 1 (p.support.image fun i ↦ puiseux_epsilon (p.coeff i))
  s.min' (Finset.insert_nonempty _ _)

private theorem puiseux_nonneg_of_coeff_ne_zero {K : Type*} [Field K]
    (x : puiseuxValuationRing K) {q : Rat}
    (hq : (x : HahnSeries Rat K).coeff q ≠ 0) : 0 ≤ q := by
  have hxnonneg : (0 : WithTop Rat) ≤ (x : HahnSeries Rat K).orderTop := by
    have hiff : (x : HahnSeries Rat K) ∈ (puiseux_hahnVal K).valuationSubring ↔
        0 ≤ (x : HahnSeries Rat K).orderTop := by
      rw [Valuation.mem_valuationSubring_iff]
      rfl
    exact hiff.mp x.property
  exact_mod_cast hxnonneg.trans (HahnSeries.orderTop_le_of_coeff_ne_zero hq)

private def puiseux_residueHom {K : Type*} [Field K] :
    puiseuxValuationRing K →+* K where
  toFun x := (x : HahnSeries Rat K).coeff 0
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by simp
  map_mul' x y := by
    change (((x : puiseuxValuationRing K) : HahnSeries Rat K) *
      ((y : puiseuxValuationRing K) : HahnSeries Rat K)).coeff 0 = _
    rw [HahnSeries.coeff_mul]
    rw [Finset.sum_eq_single (0, 0)]
    · rintro ⟨a, b⟩ hab hne
      simp only [Finset.mem_antidiagonal, HahnSeries.mem_support] at hab
      have ha : 0 ≤ a := puiseux_nonneg_of_coeff_ne_zero x hab.1
      have hb : 0 ≤ b := puiseux_nonneg_of_coeff_ne_zero y hab.2.1
      have haz : a = 0 := by linarith [hab.2.2]
      have hbz : b = 0 := by linarith [hab.2.2]
      exact (hne (by simp [haz, hbz])).elim
    · intro hnot
      have hpair : ¬ ((x : HahnSeries Rat K).coeff 0 ≠ 0 ∧
          (y : HahnSeries Rat K).coeff 0 ≠ 0) := by
        rintro ⟨hx, hy⟩
        apply hnot
        exact Finset.mem_antidiagonal.mpr ⟨
          (HahnSeries.mem_support _ _).2 hx,
          (HahnSeries.mem_support _ _).2 hy, by simp⟩
      by_cases hx : (x : HahnSeries Rat K).coeff 0 = 0
      · simp [hx]
      · have hy : (y : HahnSeries Rat K).coeff 0 = 0 := by
          by_contra hy
          exact hpair ⟨hx, hy⟩
        simp [hy]

private def puiseux_residuePolynomial {K : Type*} [Field K]
    (p : (puiseuxValuationRing K)[X]) : K[X] :=
  p.map puiseux_residueHom
namespace puiseux

private abbrev O (K : Type*) [Field K] := puiseuxValuationRing K

private def lowerSupport {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) : Finset ℕ :=
  f.support.erase f.natDegree

private theorem lowerSupport_nonempty {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
    (hpow : f ≠ X ^ f.natDegree) : (lowerSupport f).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  apply hpow
  ext i
  by_cases hi : i = f.natDegree
  · subst i
    rw [hf.coeff_natDegree]
    simp
  · have hisupp : i ∉ f.support := by
      intro hisupp
      have hiLower : i ∈ lowerSupport f :=
        Finset.mem_erase.mpr ⟨hi, hisupp⟩
      rw [hempty] at hiLower
      simp at hiLower
    rw [Polynomial.notMem_support_iff.mp hisupp]
    simp [Polynomial.coeff_X_pow, hi]

private def newtonRatio {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (i : ℕ) : Rat :=
  (f.coeff i).order / ((f.natDegree - i : ℕ) : Rat)

private noncomputable def newtonSlope {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
    (hpow : f ≠ X ^ f.natDegree) : Rat :=
  let s := (lowerSupport f).image (newtonRatio f)
  s.min' (Finset.image_nonempty.mpr (lowerSupport_nonempty f hf hpow))

private theorem newtonSlope_le_ratio {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
    (hpow : f ≠ X ^ f.natDegree) {i : ℕ} (hi : i ∈ lowerSupport f) :
    newtonSlope f hf hpow ≤ newtonRatio f i := by
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

private theorem exists_newtonSlope_eq_ratio {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
    (hpow : f ≠ X ^ f.natDegree) :
    ∃ i ∈ lowerSupport f, newtonSlope f hf hpow = newtonRatio f i := by
  let s := (lowerSupport f).image (newtonRatio f)
  have hmem := s.min'_mem
    (Finset.image_nonempty.mpr (lowerSupport_nonempty f hf hpow))
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmem
  exact ⟨i, hi, by simpa [newtonSlope, s] using heq.symm⟩

private theorem lowerSupport_lt_natDegree {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) {i : ℕ} (hi : i ∈ lowerSupport f) :
    i < f.natDegree := by
  have hi' := Finset.mem_erase.mp hi
  exact lt_of_le_of_ne (Polynomial.le_natDegree_of_mem_supp i hi'.2) hi'.1

private theorem newtonSlope_mul_le_order {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
    (hpow : f ≠ X ^ f.natDegree) {i : ℕ} (hi : i ∈ lowerSupport f) :
    ((f.natDegree - i : ℕ) : Rat) * newtonSlope f hf hpow ≤
      (f.coeff i).order := by
  have hpos : (0 : Rat) < (f.natDegree - i : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt (lowerSupport_lt_natDegree f hi)
  have hle := newtonSlope_le_ratio f hf hpow hi
  rw [newtonRatio] at hle
  simpa [mul_comm] using (le_div_iff₀ hpos).mp hle

private def scaledCoeff {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (s : Rat) (i : ℕ) : HahnSeries Rat K :=
  HahnSeries.single (((i : Rat) - (f.natDegree : Rat)) * s) 1 * f.coeff i

private theorem scaledCoeff_orderTop_nonneg {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
    (hpow : f ≠ X ^ f.natDegree) (i : ℕ) (hi : i ≤ f.natDegree) :
    (0 : WithTop Rat) ≤ (scaledCoeff f (newtonSlope f hf hpow) i).orderTop := by
  by_cases hcoeff : f.coeff i = 0
  · simp [scaledCoeff, hcoeff]
  · rw [scaledCoeff, HahnSeries.orderTop_mul,
      HahnSeries.orderTop_single one_ne_zero,
      ← HahnSeries.order_eq_orderTop_of_ne_zero hcoeff]
    apply WithTop.coe_le_coe.mpr
    by_cases hin : i = f.natDegree
    · subst i
      rw [hf.coeff_natDegree, HahnSeries.order_one]
      simp
    · have hiLower : i ∈ lowerSupport f := by
        apply Finset.mem_erase.mpr
        exact ⟨hin, Polynomial.mem_support_iff.mpr hcoeff⟩
      have hbound := newtonSlope_mul_le_order f hf hpow hiLower
      have hcast : ((f.natDegree - i : ℕ) : Rat) =
          (f.natDegree : Rat) - (i : Rat) := by
        rw [Nat.cast_sub hi]
      rw [hcast] at hbound
      linarith

private def integralScaledCoeff {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
    (hpow : f ≠ X ^ f.natDegree) (i : Fin (f.natDegree + 1)) : O K :=
  ⟨scaledCoeff f (newtonSlope f hf hpow) i, by
    rw [show scaledCoeff f (newtonSlope f hf hpow) i ∈
        (puiseux_hahnVal K).valuationSubring ↔
      0 ≤ (scaledCoeff f (newtonSlope f hf hpow) i).orderTop by
        rw [Valuation.mem_valuationSubring_iff]
        rfl]
    exact scaledCoeff_orderTop_nonneg f hf hpow i
      (Nat.lt_succ_iff.mp i.isLt)⟩

private noncomputable def newtonPolynomial {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
    (hpow : f ≠ X ^ f.natDegree) : (O K)[X] := by
  classical
  exact Polynomial.ofFn (f.natDegree + 1) (integralScaledCoeff f hf hpow)

private theorem exists_residuePolynomial_coeff_ne_zero {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
    (hpow : f ≠ X ^ f.natDegree) :
    ∃ i < f.natDegree,
      (puiseux_residuePolynomial (newtonPolynomial f hf hpow)).coeff i ≠ 0 := by
  obtain ⟨i, hiLower, hslope⟩ := exists_newtonSlope_eq_ratio f hf hpow
  have hi : i < f.natDegree := lowerSupport_lt_natDegree f hiLower
  have hcoeff : f.coeff i ≠ 0 :=
    Polynomial.mem_support_iff.mp (Finset.mem_erase.mp hiLower).2
  have hdenom : (0 : Rat) < (f.natDegree - i : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hi
  have hmul : ((f.natDegree - i : ℕ) : Rat) *
      newtonSlope f hf hpow = (f.coeff i).order := by
    rw [hslope, newtonRatio]
    simpa [mul_comm] using
      (div_mul_cancel₀ (f.coeff i).order hdenom.ne')
  have hcast : ((f.natDegree - i : ℕ) : Rat) =
      (f.natDegree : Rat) - (i : Rat) := by
    rw [Nat.cast_sub hi.le]
  rw [hcast] at hmul
  have horder : (scaledCoeff f (newtonSlope f hf hpow) i).orderTop =
      (0 : Rat) := by
    rw [scaledCoeff, HahnSeries.orderTop_mul,
      HahnSeries.orderTop_single one_ne_zero,
      ← HahnSeries.order_eq_orderTop_of_ne_zero hcoeff]
    apply WithTop.coe_eq_coe.mpr
    linarith
  refine ⟨i, hi, ?_⟩
  rw [puiseux_residuePolynomial, Polynomial.coeff_map]
  change (((newtonPolynomial f hf hpow).coeff i : O K) :
    HahnSeries Rat K).coeff 0 ≠ 0
  rw [coe_coeff_newtonPolynomial f hf hpow i hi.le]
  exact HahnSeries.coeff_orderTop_ne horder

private theorem residuePolynomial_ne_X_pow {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
    (hpow : f ≠ X ^ f.natDegree) :
    puiseux_residuePolynomial (newtonPolynomial f hf hpow) ≠
      X ^ f.natDegree := by
  obtain ⟨i, hi, hcoeff⟩ := exists_residuePolynomial_coeff_ne_zero f hf hpow
  intro heq
  have heqcoeff := congrArg (fun p : K[X] ↦ p.coeff i) heq
  simp only [Polynomial.coeff_X_pow, hi.ne, reduceIte] at heqcoeff
  exact hcoeff heqcoeff

private def center {L : Type*} [Field L] (f : L[X]) : L :=
  -f.nextCoeff / (f.natDegree : L)

private def depressed {L : Type*} [Field L] (f : L[X]) : L[X] :=
  f.comp (X + C (center f))

private theorem exists_root_monic_of_natDegree_le {K : Type*} [Field K]
    [IsAlgClosed K] [CharZero K] (n : ℕ) :
    ∀ f : (HahnSeries Rat K)[X], f.Monic → 0 < f.natDegree →
      f.natDegree ≤ n → ∃ x, f.IsRoot x := by
  let _ : CharZero (HahnSeries Rat K) :=
    charZero_of_injective_ringHom
      (show Function.Injective (HahnSeries.C : K →+* HahnSeries Rat K) from
        HahnSeries.C_injective)
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro f hf hn hfn
      let d := depressed f
      have hdmonic : d.Monic := depressed_monic f hf
      have hddeg : d.natDegree = f.natDegree := depressed_natDegree f
      have hdn : 0 < d.natDegree := hddeg.symm ▸ hn
      have hdnext : d.nextCoeff = 0 := depressed_nextCoeff f hf hn
      by_cases hdpow : d = X ^ d.natDegree
      · have hdroot : d.IsRoot 0 := by
          rw [hdpow, Polynomial.IsRoot, Polynomial.eval_pow, Polynomial.eval_X]
          exact zero_pow hdn.ne'
        exact ⟨center f, by simpa using root_of_root_depressed f hdroot⟩
      · let p := newtonPolynomial d hdmonic hdpow
        let r := puiseux_residuePolynomial p
        have hpmonic : p.Monic := newtonPolynomial_monic d hdmonic hdpow
        have hrmonic : r.Monic := residuePolynomial_monic d hdmonic hdpow
        have hrdeg : r.natDegree = d.natDegree :=
          residuePolynomial_natDegree d hdmonic hdpow
        have hrnext : r.nextCoeff = 0 :=
          residuePolynomial_nextCoeff_eq_zero d hdmonic hdn hdnext hdpow
        have hrpow : r ≠ X ^ d.natDegree :=
          residuePolynomial_ne_X_pow d hdmonic hdpow
        obtain ⟨g, q, hg, hq, hrfac, hcop, hgpos, hglt, _, _⟩ :=
          split_residue r d.natDegree hrmonic hdn hrdeg hrnext hrpow
        obtain ⟨G, Q, hG, hQ, hpGQ, hGdeg, _⟩ :=
          puiseux_lift_factorization p hpmonic g q hg hq hrfac hcop
        let σ := ValuationSubring.subtype (O K)
        let GF : (HahnSeries Rat K)[X] := G.map σ
        let QF : (HahnSeries Rat K)[X] := Q.map σ
        have hGFmonic : GF.Monic := hG.map σ
        have hGFdeg : GF.natDegree = g.natDegree := by
          exact hG.natDegree_map σ |>.trans hGdeg
        have hGFpos : 0 < GF.natDegree := hGFdeg.symm ▸ hgpos
        have hGFlt : GF.natDegree < n := by
          rw [hGFdeg]
          exact hglt.trans_le (hddeg.trans_le hfn)
        obtain ⟨x, hx⟩ := ih GF.natDegree hGFlt GF hGFmonic hGFpos le_rfl
        have hpmap : p.map σ = GF * QF := by
          rw [hpGQ, Polynomial.map_mul]
        have hpx : (p.map σ).IsRoot x := by
          rw [hpmap]
          exact Polynomial.root_mul_right_of_isRoot QF hx
        have hdx := root_of_root_newtonPolynomial d hdmonic hdpow hpx
        exact
          ⟨HahnSeries.single (newtonSlope d hdmonic hdpow) 1 * x + center f,
            root_of_root_depressed f hdx⟩

private theorem exists_root_monic {K : Type*} [Field K]
    [IsAlgClosed K] [CharZero K] (f : (HahnSeries Rat K)[X])
    (hf : f.Monic) (hn : 0 < f.natDegree) : ∃ x, f.IsRoot x :=
  exists_root_monic_of_natDegree_le (K := K) f.natDegree f hf hn le_rfl

private theorem hahnSeries_isAlgClosed {K : Type*} [Field K]
    [IsAlgClosed K] [CharZero K] : IsAlgClosed (HahnSeries Rat K) := by
  apply IsAlgClosed.of_exists_root
  intro f hf hirr
  exact exists_root_monic f hf
    (natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hirr))

end puiseux

end

namespace HahnSeries

noncomputable section

end
end HahnSeries
namespace MetaMathlibExt
noncomputable section
private def puiseux_indexHom (n : ℕ) : ℤ →+ Rat where
  toFun m := (m : Rat) / (n : Rat)
  map_zero' := by simp
  map_add' a b := by push_cast; ring

private theorem puiseux_indexHom_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (puiseux_indexHom n) := by
  intro a b hab
  apply Int.cast_injective (α := Rat)
  exact (div_left_inj' (by exact_mod_cast hn.ne')).mp hab

private theorem puiseux_indexHom_le_iff {n : ℕ} (hn : 0 < n) (a b : ℤ) :
    puiseux_indexHom n a ≤ puiseux_indexHom n b ↔ a ≤ b := by
  rw [show puiseux_indexHom n a = (a : Rat) / (n : Rat) from rfl,
    show puiseux_indexHom n b = (b : Rat) / (n : Rat) from rfl,
    div_le_div_iff_of_pos_right (by exact_mod_cast hn)]
  norm_cast

private def puiseux_indexEmbedding (n : ℕ) (hn : 0 < n) : ℤ ↪o Rat where
  toFun := puiseux_indexHom n
  inj' := puiseux_indexHom_injective hn
  map_rel_iff' := by
    intro a b
    change puiseux_indexHom n a ≤ puiseux_indexHom n b ↔ a ≤ b
    exact puiseux_indexHom_le_iff hn a b

private theorem puiseux_indexEmbedding_apply {n : ℕ} (hn : 0 < n) (m : ℤ) :
    puiseux_indexEmbedding n hn m = (m : Rat) / (n : Rat) :=
  rfl

private noncomputable def puiseux_levelHom {K : Type*} [Field K] (n : ℕ) (hn : 0 < n) :
    LaurentSeries K →+* HahnSeries Rat K :=
  HahnSeries.embDomainRingHom (puiseux_indexHom n) (puiseux_indexHom_injective hn)
    (puiseux_indexHom_le_iff hn)

private theorem puiseux_levelHom_apply {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (x : LaurentSeries K) :
    puiseux_levelHom n hn x = HahnSeries.embDomain (puiseux_indexEmbedding n hn) x :=
  rfl

private def puiseuxAtLevel {K : Type*} [Field K] (n : ℕ) (x : HahnSeries Rat K) : Prop :=
  ∀ r : Rat, HahnSeries.coeff x r ≠ 0 → ∃ m : ℤ, r = (m : Rat) / (n : Rat)

private theorem puiseux_levelHom_atLevel {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (x : LaurentSeries K) : puiseuxAtLevel n (puiseux_levelHom n hn x) := by
  intro r hr
  have hrange : r ∈ Set.range (puiseux_indexEmbedding n hn) := by
    by_contra h
    rw [puiseux_levelHom_apply hn,
      HahnSeries.embDomain_of_notMem_range (f := puiseux_indexEmbedding n hn) h] at hr
    exact hr rfl
  obtain ⟨m, rfl⟩ := hrange
  exact ⟨m, rfl⟩

private noncomputable def puiseux_pullback {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (x : HahnSeries Rat K) : LaurentSeries K :=
  HahnSeries.mk (fun m : ℤ ↦ x.coeff (puiseux_indexEmbedding n hn m)) <| by
    apply Set.IsWF.isPWO
    have h := Set.WellFoundedOn.mapsTo (puiseux_indexEmbedding n hn) (s := x.support)
      (t := Function.support fun m : ℤ ↦ x.coeff (puiseux_indexEmbedding n hn m))
      (by
        intro m hm
        exact (HahnSeries.mem_support x _).2 hm)
      x.isWF_support
    exact h.mono' fun a _ b _ hab ↦ (puiseux_indexEmbedding n hn).lt_iff_lt.mpr hab

private theorem puiseux_levelHom_pullback {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (x : HahnSeries Rat K) (hx : puiseuxAtLevel n x) :
    puiseux_levelHom n hn (puiseux_pullback hn x) = x := by
  ext r
  by_cases hr : r ∈ Set.range (puiseux_indexEmbedding n hn)
  · obtain ⟨m, rfl⟩ := hr
    simp [puiseux_levelHom_apply, puiseux_pullback]
  · rw [puiseux_levelHom_apply,
      HahnSeries.embDomain_of_notMem_range (f := puiseux_indexEmbedding n hn) hr]
    symm
    by_contra hcoeff
    obtain ⟨m, hm⟩ := hx r hcoeff
    apply hr
    exact ⟨m, hm.symm⟩

private theorem puiseux_atLevel_iff {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (x : HahnSeries Rat K) :
    puiseuxAtLevel n x ↔ ∃ z : LaurentSeries K, puiseux_levelHom n hn z = x := by
  constructor
  · intro hx
    exact ⟨puiseux_pullback hn x, puiseux_levelHom_pullback hn x hx⟩
  · rintro ⟨z, rfl⟩
    exact puiseux_levelHom_atLevel hn z

private def puiseuxBounded {K : Type*} [Field K] (x : HahnSeries Rat K) : Prop :=
  ∃ n : ℕ, 0 < n ∧ puiseuxAtLevel n x

private theorem puiseux_atLevel_mul_denominator {K : Type*} [Field K] {n k : ℕ}
    (hn : 0 < n) (hk : 0 < k) {x : HahnSeries Rat K} (hx : puiseuxAtLevel n x) :
    puiseuxAtLevel (n * k) x := by
  intro r hr
  obtain ⟨m, rfl⟩ := hx r hr
  refine ⟨m * (k : ℤ), ?_⟩
  push_cast
  field_simp [hn.ne', hk.ne']

private theorem puiseux_bounded_zero {K : Type*} [Field K] :
    puiseuxBounded (0 : HahnSeries Rat K) := by
  refine ⟨1, by norm_num, ?_⟩
  simpa using puiseux_levelHom_atLevel (K := K) (n := 1) (by norm_num)
    (0 : LaurentSeries K)

private theorem puiseux_bounded_one {K : Type*} [Field K] :
    puiseuxBounded (1 : HahnSeries Rat K) := by
  refine ⟨1, by norm_num, ?_⟩
  simpa using puiseux_levelHom_atLevel (K := K) (n := 1) (by norm_num)
    (1 : LaurentSeries K)

private theorem puiseux_bounded_neg {K : Type*} [Field K] {x : HahnSeries Rat K}
    (hx : puiseuxBounded x) : puiseuxBounded (-x) := by
  obtain ⟨n, hn, hx⟩ := hx
  refine ⟨n, hn, (puiseux_atLevel_iff hn (-x)).2 ?_⟩
  obtain ⟨z, rfl⟩ := (puiseux_atLevel_iff hn x).1 hx
  exact ⟨-z, map_neg (puiseux_levelHom n hn) z⟩

private theorem puiseux_bounded_inv {K : Type*} [Field K] {x : HahnSeries Rat K}
    (hx : puiseuxBounded x) : puiseuxBounded x⁻¹ := by
  obtain ⟨n, hn, hx⟩ := hx
  refine ⟨n, hn, (puiseux_atLevel_iff hn x⁻¹).2 ?_⟩
  obtain ⟨z, rfl⟩ := (puiseux_atLevel_iff hn x).1 hx
  exact ⟨z⁻¹, map_inv₀ (puiseux_levelHom n hn) z⟩

private theorem puiseux_common_level {K : Type*} [Field K] {x y : HahnSeries Rat K}
    (hx : puiseuxBounded x) (hy : puiseuxBounded y) :
    ∃ n : ℕ, 0 < n ∧ puiseuxAtLevel n x ∧ puiseuxAtLevel n y := by
  obtain ⟨n, hn, hx⟩ := hx
  obtain ⟨m, hm, hy⟩ := hy
  refine ⟨n * m, Nat.mul_pos hn hm, puiseux_atLevel_mul_denominator hn hm hx, ?_⟩
  simpa [Nat.mul_comm] using puiseux_atLevel_mul_denominator hm hn hy

private theorem puiseux_bounded_add {K : Type*} [Field K] {x y : HahnSeries Rat K}
    (hx : puiseuxBounded x) (hy : puiseuxBounded y) : puiseuxBounded (x + y) := by
  obtain ⟨n, hn, hxn, hyn⟩ := puiseux_common_level hx hy
  refine ⟨n, hn, (puiseux_atLevel_iff hn (x + y)).2 ?_⟩
  obtain ⟨zx, hzx⟩ := (puiseux_atLevel_iff hn x).1 hxn
  obtain ⟨zy, hzy⟩ := (puiseux_atLevel_iff hn y).1 hyn
  exact ⟨zx + zy, by rw [map_add, hzx, hzy]⟩

private theorem puiseux_bounded_mul {K : Type*} [Field K] {x y : HahnSeries Rat K}
    (hx : puiseuxBounded x) (hy : puiseuxBounded y) : puiseuxBounded (x * y) := by
  obtain ⟨n, hn, hxn, hyn⟩ := puiseux_common_level hx hy
  refine ⟨n, hn, (puiseux_atLevel_iff hn (x * y)).2 ?_⟩
  obtain ⟨zx, hzx⟩ := (puiseux_atLevel_iff hn x).1 hxn
  obtain ⟨zy, hzy⟩ := (puiseux_atLevel_iff hn y).1 hyn
  exact ⟨zx * zy, by rw [map_mul, hzx, hzy]⟩

private def puiseuxSubfield (K : Type*) [Field K] : Subfield (HahnSeries Rat K) where
  carrier := {x | puiseuxBounded x}
  zero_mem' := puiseux_bounded_zero
  one_mem' := puiseux_bounded_one
  add_mem' := fun hx hy ↦ puiseux_bounded_add hx hy
  mul_mem' := fun hx hy ↦ puiseux_bounded_mul hx hy
  neg_mem' := fun hx ↦ puiseux_bounded_neg hx
  inv_mem' := fun _ hx ↦ puiseux_bounded_inv hx

private theorem puiseux_bounded_natCast {K : Type*} [Field K] (n : ℕ) :
    puiseuxBounded (n : HahnSeries Rat K) := by
  induction n with
  | zero => simpa using (puiseux_bounded_zero (K := K))
  | succ n ih =>
      simpa [Nat.cast_succ] using
        puiseux_bounded_add ih (puiseux_bounded_one (K := K))

private def puiseuxPolynomialBounded {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) : Prop :=
  ∀ i, puiseuxBounded (f.coeff i)

private noncomputable def puiseux_subfieldPolynomial {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : puiseuxPolynomialBounded f) :
    (↥(puiseuxSubfield K))[X] := by
  classical
  exact Polynomial.ofFn (f.natDegree + 1) fun i ↦ ⟨f.coeff i, hf i⟩

private theorem puiseux_bounded_nextCoeff {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : puiseuxPolynomialBounded f) :
    puiseuxBounded f.nextCoeff := by
  by_cases hn : f.natDegree = 0
  · simp [Polynomial.nextCoeff, hn, puiseux_bounded_zero]
  · simpa [Polynomial.nextCoeff, hn] using hf (f.natDegree - 1)

private theorem puiseux_bounded_center {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : puiseuxPolynomialBounded f) :
    puiseuxBounded (puiseux.center f) := by
  rw [puiseux.center, div_eq_mul_inv]
  exact puiseux_bounded_mul
    (puiseux_bounded_neg (puiseux_bounded_nextCoeff f hf))
    (puiseux_bounded_inv (puiseux_bounded_natCast f.natDegree))

private theorem puiseux_depressed_bounded {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : puiseuxPolynomialBounded f) :
    puiseuxPolynomialBounded (puiseux.depressed f) := by
  let c : ↥(puiseuxSubfield K) := ⟨puiseux.center f, puiseux_bounded_center f hf⟩
  let q : (↥(puiseuxSubfield K))[X] :=
    (puiseux_subfieldPolynomial f hf).comp (X + C c)
  apply puiseux_polynomialBounded_of_eq_map q
  simp [q, c, puiseux.depressed, Polynomial.map_comp,
    puiseux_map_subfieldPolynomial]

private theorem puiseux_newtonPolynomial_bounded {K : Type*} [Field K]
    (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
    (hpow : f ≠ X ^ f.natDegree) (hbounded : puiseuxPolynomialBounded f) :
    ∀ i, puiseuxBounded
      (((puiseux.newtonPolynomial f hf hpow).coeff i :
        puiseuxValuationRing K) : HahnSeries Rat K) := by
  intro i
  by_cases hi : i ≤ f.natDegree
  · rw [puiseux.coe_coeff_newtonPolynomial f hf hpow i hi]
    exact puiseux_bounded_mul
      (puiseux_bounded_single _ 1) (hbounded i)
  · have hlt : f.natDegree < i := Nat.lt_of_not_ge hi
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt <|
      (puiseux.newtonPolynomial_natDegree f hf hpow).symm ▸ hlt]
    exact puiseux_bounded_zero

private noncomputable def puiseux_powerSeriesLevelHom {K : Type*} [Field K]
    (n : ℕ) (hn : 0 < n) : PowerSeries K →+* HahnSeries Rat K :=
  (puiseux_levelHom n hn).comp (HahnSeries.ofPowerSeries ℤ K)

private theorem puiseux_powerSeriesLevelHom_apply {K : Type*} [Field K]
    {n : ℕ} (hn : 0 < n) (x : PowerSeries K) :
    puiseux_powerSeriesLevelHom n hn x =
      puiseux_levelHom n hn (x : LaurentSeries K) :=
  rfl

private theorem puiseux_powerSeriesLevelHom_atLevel {K : Type*} [Field K]
    {n : ℕ} (hn : 0 < n) (x : PowerSeries K) :
    puiseuxAtLevel n (puiseux_powerSeriesLevelHom n hn x) := by
  rw [puiseux_powerSeriesLevelHom_apply]
  exact puiseux_levelHom_atLevel hn (x : LaurentSeries K)

private theorem puiseux_powerSeriesLevelHom_orderTop_nonneg
    {K : Type*} [Field K] {n : ℕ} (hn : 0 < n) (x : PowerSeries K) :
    (0 : WithTop Rat) ≤ (puiseux_powerSeriesLevelHom n hn x).orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro r hr
  by_cases hrange : r ∈ Set.range (puiseux_indexEmbedding n hn)
  · obtain ⟨m, rfl⟩ := hrange
    rw [puiseux_powerSeriesLevelHom_apply, puiseux_levelHom_apply,
      HahnSeries.embDomain_coeff, PowerSeries.coeff_coe]
    have hq : (puiseux_indexEmbedding n hn m : Rat) < 0 := by
      exact_mod_cast hr
    rw [puiseux_indexEmbedding_apply] at hq
    have hnq : (0 : Rat) < n := by exact_mod_cast hn
    have hm : m < 0 := by
      rcases div_neg_iff.mp hq with h | h
      · exact (not_lt_of_ge hnq.le h.2).elim
      · exact_mod_cast h.1
    simp [hm]
  · rw [puiseux_powerSeriesLevelHom_apply, puiseux_levelHom_apply,
      HahnSeries.embDomain_of_notMem_range (f := puiseux_indexEmbedding n hn) hrange]

private noncomputable def puiseux_powerSeriesToValuationRing
    {K : Type*} [Field K] (n : ℕ) (hn : 0 < n) :
    PowerSeries K →+* puiseuxValuationRing K :=
  (puiseux_powerSeriesLevelHom n hn).codRestrict
    (puiseux_hahnVal K).valuationSubring fun x ↦ by
      rw [show puiseux_powerSeriesLevelHom n hn x ∈
          (puiseux_hahnVal K).valuationSubring ↔
        0 ≤ (puiseux_powerSeriesLevelHom n hn x).orderTop by
          rw [Valuation.mem_valuationSubring_iff]
          rfl]
      exact puiseux_powerSeriesLevelHom_orderTop_nonneg hn x

private theorem puiseux_residue_powerSeriesToValuationRing
    {K : Type*} [Field K] {n : ℕ} (hn : 0 < n) (x : PowerSeries K) :
    puiseux_residueHom (puiseux_powerSeriesToValuationRing n hn x) =
      PowerSeries.constantCoeff x := by
  change (puiseux_powerSeriesLevelHom n hn x).coeff 0 =
    PowerSeries.constantCoeff x
  rw [puiseux_powerSeriesLevelHom_apply, puiseux_levelHom_apply]
  rw [← show puiseux_indexEmbedding n hn (0 : ℤ) = 0 by
    simp [puiseux_indexEmbedding_apply]]
  rw [HahnSeries.embDomain_coeff]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact HahnSeries.ofPowerSeries_apply_coeff x 0

private theorem puiseux_exists_powerSeries_preimage {K : Type*} [Field K]
    {n : ℕ} (hn : 0 < n) (x : puiseuxValuationRing K)
    (hx : puiseuxAtLevel n (x : HahnSeries Rat K)) :
    ∃ z : PowerSeries K, puiseux_powerSeriesToValuationRing n hn z = x := by
  let l : LaurentSeries K := puiseux_pullback hn (x : HahnSeries Rat K)
  let z : PowerSeries K := PowerSeries.mk fun k ↦ l.coeff (k : ℤ)
  have hz : (z : LaurentSeries K) = l := by
    ext m
    rw [PowerSeries.coeff_coe]
    by_cases hm : m < 0
    · simp only [hm, reduceIte]
      symm
      by_contra hlm
      have hxcoeff : (x : HahnSeries Rat K).coeff
          (puiseux_indexEmbedding n hn m) ≠ 0 := by
        simpa [l, puiseux_pullback] using hlm
      have hnonneg := puiseux_nonneg_of_coeff_ne_zero x hxcoeff
      have hmrat : (m : Rat) < 0 := by exact_mod_cast hm
      have hnrat : (0 : Rat) < n := by exact_mod_cast hn
      have hneg : puiseux_indexEmbedding n hn m < 0 := by
        rw [puiseux_indexEmbedding_apply]
        exact div_neg_of_neg_of_pos hmrat hnrat
      exact (not_le_of_gt hneg) hnonneg
    · simp only [hm, reduceIte]
      rw [show PowerSeries.coeff m.natAbs z = l.coeff (m.natAbs : ℤ) by
        simp [z]]
      congr 1
      exact (Int.eq_natAbs_of_nonneg (le_of_not_gt hm)).symm
  refine ⟨z, ?_⟩
  apply Subtype.ext
  change puiseux_powerSeriesLevelHom n hn z = (x : HahnSeries Rat K)
  rw [puiseux_powerSeriesLevelHom_apply, hz]
  exact puiseux_levelHom_pullback hn (x : HahnSeries Rat K) hx

private theorem puiseux_common_level_finset {K α : Type*} [Field K]
    (s : Finset α) (x : α → HahnSeries Rat K)
    (hx : ∀ i ∈ s, puiseuxBounded (x i)) :
    ∃ n : ℕ, 0 < n ∧ ∀ i ∈ s, puiseuxAtLevel n (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨1, by norm_num, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨n, hn, hsn⟩ := ih fun i hi ↦ hx i (Finset.mem_insert_of_mem hi)
      obtain ⟨m, hm, ham⟩ := hx a (Finset.mem_insert_self a s)
      refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact puiseux_atLevel_mul_denominator hm hn ham
      · simpa [Nat.mul_comm] using
          puiseux_atLevel_mul_denominator hn hm (hsn i hi)

private theorem puiseux_polynomial_common_level {K : Type*} [Field K]
    (p : (HahnSeries Rat K)[X])
    (hp : ∀ i, puiseuxBounded (p.coeff i)) :
    ∃ n : ℕ, 0 < n ∧ ∀ i, puiseuxAtLevel n (p.coeff i) := by
  obtain ⟨n, hn, hs⟩ :=
    puiseux_common_level_finset p.support (fun i ↦ p.coeff i)
      (fun i _ ↦ hp i)
  refine ⟨n, hn, fun i ↦ ?_⟩
  by_cases hi : i ∈ p.support
  · exact hs i hi
  · rw [Polynomial.notMem_support_iff.mp hi]
    intro r hr
    exact (hr rfl).elim

private noncomputable def puiseux_powerSeriesPolynomial {K : Type*} [Field K]
    {n : ℕ} (hn : 0 < n) (p : (puiseuxValuationRing K)[X])
    (hp : ∀ i, puiseuxAtLevel n
      ((p.coeff i : puiseuxValuationRing K) : HahnSeries Rat K)) :
    (PowerSeries K)[X] := by
  classical
  exact Polynomial.ofFn (p.natDegree + 1) fun i ↦
    Classical.choose (puiseux_exists_powerSeries_preimage hn (p.coeff i) (hp i))

private theorem puiseux_powerSeriesPolynomial_coeff {K : Type*} [Field K]
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

private theorem puiseux_powerSeriesPolynomial_coeff_eq_zero {K : Type*}
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

private theorem puiseux_map_powerSeriesPolynomial {K : Type*} [Field K]
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

private theorem puiseux_powerSeriesPolynomial_monic {K : Type*} [Field K]
    {n : ℕ} (hn : 0 < n) (p : (puiseuxValuationRing K)[X])
    (hp : ∀ i, puiseuxAtLevel n
      ((p.coeff i : puiseuxValuationRing K) : HahnSeries Rat K))
    (hmonic : p.Monic) : (puiseux_powerSeriesPolynomial hn p hp).Monic := by
  apply Polynomial.monic_of_injective
    (puiseux_powerSeriesToValuationRing_injective hn)
  rw [puiseux_map_powerSeriesPolynomial hn p hp]
  exact hmonic

private theorem puiseux_map_constantCoeff_powerSeriesPolynomial
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

private theorem puiseux_bounded_coeff_map_powerSeries
    {K : Type*} [Field K] {n : ℕ} (hn : 0 < n) (q : (PowerSeries K)[X])
    (i : ℕ) :
    puiseuxBounded
      ((((q.map (puiseux_powerSeriesToValuationRing n hn)).coeff i :
        puiseuxValuationRing K) : HahnSeries Rat K)) := by
  rw [Polynomial.coeff_map]
  exact ⟨n, hn, puiseux_powerSeriesLevelHom_atLevel hn (q.coeff i)⟩

private theorem puiseux_lift_factorization_bounded {K : Type*} [Field K]
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

private theorem puiseux_exists_bounded_root_monic_of_natDegree_le
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

private theorem puiseux_exists_bounded_root_monic
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (f : (HahnSeries Rat K)[X]) (hf : f.Monic) (hn : 0 < f.natDegree)
    (hbounded : puiseuxPolynomialBounded f) :
    ∃ x, f.IsRoot x ∧ puiseuxBounded x :=
  puiseux_exists_bounded_root_monic_of_natDegree_le
    f.natDegree f hf hn le_rfl hbounded

private theorem puiseux_subfield_isAlgClosed {K : Type*} [Field K]
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

private noncomputable def puiseux_laurentHom {K : Type*} [Field K] :
    LaurentSeries K →+* HahnSeries Rat K :=
  puiseux_levelHom 1 (by norm_num)

private theorem puiseux_laurentHom_mem {K : Type*} [Field K] (x : LaurentSeries K) :
    puiseux_laurentHom x ∈ puiseuxSubfield K := by
  exact ⟨1, by norm_num, puiseux_levelHom_atLevel (by norm_num) x⟩

private noncomputable def puiseux_laurentToSubfield {K : Type*} [Field K] :
    LaurentSeries K →+* ↥(puiseuxSubfield K) :=
  (puiseux_laurentHom (K := K)).codRestrict (puiseuxSubfield K) puiseux_laurentHom_mem

private def puiseux_scaleIndexHom (n : ℕ) : ℤ →+ ℤ where
  toFun m := (n : ℤ) * m
  map_zero' := by simp
  map_add' a b := by ring

private theorem puiseux_scaleIndexHom_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (puiseux_scaleIndexHom n) := by
  intro a b hab
  exact mul_left_cancel₀ (by exact_mod_cast hn.ne') hab

private theorem puiseux_scaleIndexHom_le_iff {n : ℕ} (hn : 0 < n) (a b : ℤ) :
    puiseux_scaleIndexHom n a ≤ puiseux_scaleIndexHom n b ↔ a ≤ b := by
  change (n : ℤ) * a ≤ (n : ℤ) * b ↔ a ≤ b
  exact Int.mul_le_mul_left (by exact_mod_cast hn)

private def puiseux_scaleIndexEmbedding (n : ℕ) (hn : 0 < n) : ℤ ↪o ℤ where
  toFun := puiseux_scaleIndexHom n
  inj' := puiseux_scaleIndexHom_injective hn
  map_rel_iff' := by
    intro a b
    change puiseux_scaleIndexHom n a ≤ puiseux_scaleIndexHom n b ↔ a ≤ b
    exact puiseux_scaleIndexHom_le_iff hn a b

private theorem puiseux_scaleIndexEmbedding_apply {n : ℕ} (hn : 0 < n) (m : ℤ) :
    puiseux_scaleIndexEmbedding n hn m = (n : ℤ) * m :=
  rfl

private noncomputable def puiseux_scaleHom {K : Type*} [Field K] (n : ℕ) (hn : 0 < n) :
    LaurentSeries K →+* LaurentSeries K :=
  HahnSeries.embDomainRingHom (puiseux_scaleIndexHom n)
    (puiseux_scaleIndexHom_injective hn) (puiseux_scaleIndexHom_le_iff hn)

private theorem puiseux_scaleHom_apply {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (x : LaurentSeries K) :
    puiseux_scaleHom n hn x = HahnSeries.embDomain (puiseux_scaleIndexEmbedding n hn) x :=
  rfl

private theorem puiseux_index_scale {n : ℕ} (hn : 0 < n) (m : ℤ) :
    puiseux_indexEmbedding n hn (puiseux_scaleIndexEmbedding n hn m) =
      puiseux_indexEmbedding 1 (by norm_num) m := by
  rw [puiseux_scaleIndexEmbedding_apply, puiseux_indexEmbedding_apply,
    puiseux_indexEmbedding_apply]
  push_cast
  field_simp [hn.ne']

private theorem puiseux_index_one_range_subset {n : ℕ} (hn : 0 < n) :
    Set.range (puiseux_indexEmbedding 1 (by norm_num)) ⊆
      Set.range (puiseux_indexEmbedding n hn) := by
  rintro _ ⟨m, rfl⟩
  exact ⟨puiseux_scaleIndexEmbedding n hn m, puiseux_index_scale hn m⟩

private theorem puiseux_scale_mem_range_of_index_mem_one {n : ℕ} (hn : 0 < n) (a : ℤ)
    (ha : puiseux_indexEmbedding n hn a ∈
      Set.range (puiseux_indexEmbedding 1 (by norm_num))) :
    a ∈ Set.range (puiseux_scaleIndexEmbedding n hn) := by
  obtain ⟨m, hm⟩ := ha
  refine ⟨m, (puiseux_indexEmbedding n hn).injective ?_⟩
  rw [puiseux_index_scale]
  exact hm

private theorem puiseux_levelHom_scaleHom {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (x : LaurentSeries K) :
    puiseux_levelHom n hn (puiseux_scaleHom n hn x) = puiseux_laurentHom x := by
  rw [show puiseux_laurentHom x = puiseux_levelHom 1 (by norm_num) x from rfl]
  ext r
  by_cases hr : r ∈ Set.range (puiseux_indexEmbedding n hn)
  · obtain ⟨a, rfl⟩ := hr
    rw [puiseux_levelHom_apply, HahnSeries.embDomain_coeff, puiseux_scaleHom_apply]
    by_cases ha : a ∈ Set.range (puiseux_scaleIndexEmbedding n hn)
    · obtain ⟨m, rfl⟩ := ha
      rw [HahnSeries.embDomain_coeff, puiseux_index_scale, puiseux_levelHom_apply,
        HahnSeries.embDomain_coeff]
    · rw [HahnSeries.embDomain_of_notMem_range ha, puiseux_levelHom_apply,
        HahnSeries.embDomain_of_notMem_range]
      exact fun h ↦ ha (puiseux_scale_mem_range_of_index_mem_one hn a h)
  · rw [puiseux_levelHom_apply,
      HahnSeries.embDomain_of_notMem_range (f := puiseux_indexEmbedding n hn) hr,
      puiseux_levelHom_apply, HahnSeries.embDomain_of_notMem_range]
    exact fun h ↦ hr (puiseux_index_one_range_subset hn h)

private def puiseux_residueIndexEmbedding (n : ℕ) (hn : 0 < n) (r : Fin n) : ℤ ↪o ℤ where
  toFun q := (n : ℤ) * q + (r : ℕ)
  inj' := by
    intro a b hab
    apply puiseux_scaleIndexHom_injective hn
    exact add_right_cancel hab
  map_rel_iff' := by
    intro a b
    change (n : ℤ) * a + (r : ℕ) ≤ (n : ℤ) * b + (r : ℕ) ↔ a ≤ b
    rw [add_le_add_iff_right]
    exact puiseux_scaleIndexHom_le_iff hn a b

private noncomputable def puiseux_residuePart {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (r : Fin n) (x : LaurentSeries K) : LaurentSeries K :=
  HahnSeries.mk (fun q : ℤ ↦ x.coeff (puiseux_residueIndexEmbedding n hn r q)) <| by
    apply Set.IsWF.isPWO
    have h := Set.WellFoundedOn.mapsTo (puiseux_residueIndexEmbedding n hn r) (s := x.support)
      (t := Function.support fun q : ℤ ↦
        x.coeff (puiseux_residueIndexEmbedding n hn r q))
      (by
        intro q hq
        exact (HahnSeries.mem_support x _).2 hq)
      x.isWF_support
    exact h.mono' fun a _ b _ hab ↦ (puiseux_residueIndexEmbedding n hn r).lt_iff_lt.mpr hab

private def puiseux_remainderFin (n : ℕ) (hn : 0 < n) (m : ℤ) : Fin n :=
  ⟨(m % (n : ℤ)).toNat, by
    have hnonneg : 0 ≤ m % (n : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hn.ne')
    have hlt : m % (n : ℤ) < (n : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hn)
    have hcast : ((m % (n : ℤ)).toNat : ℤ) < (n : ℤ) := by
      simpa [Int.toNat_of_nonneg hnonneg] using hlt
    exact_mod_cast hcast⟩

private theorem puiseux_remainder_term_coeff {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (x : LaurentSeries K) (m : ℤ) :
    (puiseux_scaleHom n hn (puiseux_residuePart hn (puiseux_remainderFin n hn m) x) *
      HahnSeries.single ((puiseux_remainderFin n hn m : ℕ) : ℤ) 1).coeff m = x.coeff m := by
  rw [HahnSeries.coeff_mul_single, mul_one]
  have harg : m - ((puiseux_remainderFin n hn m : ℕ) : ℤ) =
      (n : ℤ) * (m / (n : ℤ)) := by
    rw [puiseux_remainderFin_val]
    linarith [Int.emod_add_mul_ediv m (n : ℤ)]
  rw [harg, puiseux_scaleHom_apply,
    ← puiseux_scaleIndexEmbedding_apply hn (m / (n : ℤ)), HahnSeries.embDomain_coeff,
    puiseux_coeff_residuePart]
  congr 1
  rw [puiseux_remainderFin_val]
  linarith [Int.emod_add_mul_ediv m (n : ℤ)]

private theorem puiseux_other_term_coeff {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (x : LaurentSeries K) (m : ℤ) (r : Fin n) (hr : r ≠ puiseux_remainderFin n hn m) :
    (puiseux_scaleHom n hn (puiseux_residuePart hn r x) *
      HahnSeries.single ((r : ℕ) : ℤ) 1).coeff m = 0 := by
  rw [HahnSeries.coeff_mul_single, mul_one, puiseux_scaleHom_apply,
    HahnSeries.embDomain_of_notMem_range]
  rintro ⟨q, hq⟩
  apply hr
  apply puiseux_residue_eq_remainder_of_eq hn m q r
  rw [puiseux_scaleIndexEmbedding_apply] at hq
  linarith

private theorem puiseux_residue_decomposition {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (x : LaurentSeries K) :
    (∑ r : Fin n, puiseux_scaleHom n hn (puiseux_residuePart hn r x) *
      HahnSeries.single ((r : ℕ) : ℤ) 1) = x := by
  ext m
  rw [HahnSeries.coeff_sum, Finset.sum_eq_single (puiseux_remainderFin n hn m)]
  · exact puiseux_remainder_term_coeff hn x m
  · intro r _ hr
    exact puiseux_other_term_coeff hn x m r hr
  · simp

private noncomputable def puiseuxLevelField (K : Type*) [Field K] (n : ℕ) (hn : 0 < n) :
    Subfield (HahnSeries Rat K) :=
  (puiseux_levelHom n hn).fieldRange

private noncomputable def puiseux_baseToLevel {K : Type*} [Field K] (n : ℕ) (hn : 0 < n) :
    LaurentSeries K →+* ↥(puiseuxLevelField K n hn) :=
  (puiseux_laurentHom (K := K)).codRestrict (puiseuxLevelField K n hn) fun x ↦ by
    rw [puiseuxLevelField, RingHom.mem_fieldRange]
    exact ⟨puiseux_scaleHom n hn x, puiseux_levelHom_scaleHom hn x⟩

@[instance_reducible]
private noncomputable def puiseux_levelAlgebra {K : Type*} [Field K] (n : ℕ) (hn : 0 < n) :
    Algebra (LaurentSeries K) ↥(puiseuxLevelField K n hn) :=
  (puiseux_baseToLevel n hn).toAlgebra

private noncomputable def puiseux_levelGenerator {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (r : Fin n) : ↥(puiseuxLevelField K n hn) :=
  ⟨puiseux_levelHom n hn (HahnSeries.single ((r : ℕ) : ℤ) 1),
    RingHom.mem_fieldRange_self _ _⟩

private theorem puiseux_level_decomposition {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (y : ↥(puiseuxLevelField K n hn)) :
    let _ : Algebra (LaurentSeries K) ↥(puiseuxLevelField K n hn) :=
      puiseux_levelAlgebra n hn
    ∃ z : LaurentSeries K, puiseux_levelHom n hn z = (y : HahnSeries Rat K) ∧
      y = ∑ r : Fin n, puiseux_residuePart hn r z • puiseux_levelGenerator hn r := by
  let _ : Algebra (LaurentSeries K) ↥(puiseuxLevelField K n hn) :=
    puiseux_levelAlgebra n hn
  obtain ⟨z, hz⟩ := (RingHom.mem_fieldRange.mp y.property)
  refine ⟨z, hz, ?_⟩
  apply Subtype.ext
  change (puiseuxLevelField K n hn).subtype y =
    (puiseuxLevelField K n hn).subtype
      (∑ r : Fin n, puiseux_residuePart hn r z • puiseux_levelGenerator hn r)
  rw [map_sum]
  simp only [Algebra.smul_def, map_mul]
  change (y : HahnSeries Rat K) =
    ∑ r : Fin n,
      ((algebraMap (LaurentSeries K) ↥(puiseuxLevelField K n hn)
        (puiseux_residuePart hn r z) : ↥(puiseuxLevelField K n hn)) : HahnSeries Rat K) *
      ((puiseux_levelGenerator (K := K) hn r : ↥(puiseuxLevelField K n hn)) :
        HahnSeries Rat K)
  have halg (a : LaurentSeries K) :
      ((algebraMap (LaurentSeries K) ↥(puiseuxLevelField K n hn) a :
        ↥(puiseuxLevelField K n hn)) : HahnSeries Rat K) = puiseux_laurentHom a := rfl
  have hgen (r : Fin n) :
      ((puiseux_levelGenerator (K := K) hn r : ↥(puiseuxLevelField K n hn)) :
        HahnSeries Rat K) =
        puiseux_levelHom n hn (HahnSeries.single ((r : ℕ) : ℤ) 1) := rfl
  simp_rw [halg, hgen]
  rw [← hz]
  calc
    puiseux_levelHom n hn z =
        puiseux_levelHom n hn
          (∑ r : Fin n, puiseux_scaleHom n hn (puiseux_residuePart hn r z) *
            HahnSeries.single ((r : ℕ) : ℤ) 1) :=
      congrArg (puiseux_levelHom n hn) (puiseux_residue_decomposition hn z).symm
    _ = _ := by simp only [map_sum, map_mul, puiseux_levelHom_scaleHom]

private theorem puiseux_level_module_finite {K : Type*} [Field K] {n : ℕ} (hn : 0 < n) :
    @Module.Finite (LaurentSeries K) ↥(puiseuxLevelField K n hn) inferInstance inferInstance
      (puiseux_levelAlgebra n hn).toModule := by
  let _ : Algebra (LaurentSeries K) ↥(puiseuxLevelField K n hn) :=
    puiseux_levelAlgebra n hn
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨Set.range (puiseux_levelGenerator (K := K) hn), Set.finite_range _, ?_⟩
  apply top_unique
  intro y _
  obtain ⟨z, _, hy⟩ := puiseux_level_decomposition hn y
  rw [hy]
  apply Submodule.sum_mem
  intro r _
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self r))

@[instance_reducible]
private noncomputable def puiseux_subfieldAlgebra {K : Type*} [Field K] :
    Algebra (LaurentSeries K) ↥(puiseuxSubfield K) :=
  (puiseux_laurentToSubfield (K := K)).toAlgebra

private noncomputable def puiseux_levelToSubfield {K : Type*} [Field K] {n : ℕ}
    (hn : 0 < n) : ↥(puiseuxLevelField K n hn) →+* ↥(puiseuxSubfield K) :=
  (puiseuxLevelField K n hn).subtype.codRestrict (puiseuxSubfield K) fun y ↦ by
    obtain ⟨z, hz⟩ := RingHom.mem_fieldRange.mp y.property
    change (y : HahnSeries Rat K) ∈ puiseuxSubfield K
    rw [← hz]
    exact ⟨n, hn, puiseux_levelHom_atLevel hn z⟩

private noncomputable def puiseux_levelToSubfieldAlgHom {K : Type*} [Field K] {n : ℕ}
    (hn : 0 < n) :
    let _ : Algebra (LaurentSeries K) ↥(puiseuxLevelField K n hn) :=
      puiseux_levelAlgebra n hn
    let _ : Algebra (LaurentSeries K) ↥(puiseuxSubfield K) := puiseux_subfieldAlgebra
    ↥(puiseuxLevelField K n hn) →ₐ[LaurentSeries K] ↥(puiseuxSubfield K) := by
  let _ : Algebra (LaurentSeries K) ↥(puiseuxLevelField K n hn) :=
    puiseux_levelAlgebra n hn
  let _ : Algebra (LaurentSeries K) ↥(puiseuxSubfield K) := puiseux_subfieldAlgebra
  exact
    { puiseux_levelToSubfield hn with
      commutes' := fun _ ↦ rfl }

private theorem puiseux_subfield_isAlgebraic {K : Type*} [Field K] :
    let _ : Algebra (LaurentSeries K) ↥(puiseuxSubfield K) := puiseux_subfieldAlgebra
    Algebra.IsAlgebraic (LaurentSeries K) ↥(puiseuxSubfield K) := by
  let _ : Algebra (LaurentSeries K) ↥(puiseuxSubfield K) := puiseux_subfieldAlgebra
  constructor
  intro x
  obtain ⟨n, hn, hx⟩ := x.property
  obtain ⟨z, hz⟩ := (puiseux_atLevel_iff hn (x : HahnSeries Rat K)).1 hx
  let y : ↥(puiseuxLevelField K n hn) :=
    ⟨x, by
      rw [puiseuxLevelField, RingHom.mem_fieldRange]
      exact ⟨z, hz⟩⟩
  let _ : Algebra (LaurentSeries K) ↥(puiseuxLevelField K n hn) :=
    puiseux_levelAlgebra n hn
  let _ : Module.Finite (LaurentSeries K) ↥(puiseuxLevelField K n hn) :=
    puiseux_level_module_finite hn
  have hy : IsIntegral (LaurentSeries K) y :=
    (IsAlgebraic.of_finite (LaurentSeries K) y).isIntegral
  have hmap := hy.map (puiseux_levelToSubfieldAlgHom hn)
  have heq : puiseux_levelToSubfieldAlgHom hn y = x := by
    apply Subtype.ext
    rfl
  rw [heq] at hmap
  exact hmap.isAlgebraic

/-- Puiseux's theorem (https://en.wikipedia.org/wiki/Puiseux_series):
The set of Puiseux series over an algebraically closed field of characteristic
zero is itself an algebraically closed field (the field of Puiseux series).
Puiseux series are modelled as `HahnSeries Rat K`. The Puiseux field is carried
as the bounded-denominator subfield of `HahnSeries Rat K` (the union over `n`
of `K((t ^ (1 / n)))`, i.e. each series has support denominators dividing some
`n` depending on the series), and it is the algebraic closure of the field of
formal Laurent series, which itself is the field of fractions of the ring of
formal power series.

Proves `Wanted` entry `puiseux_theorem`.

Proof: Newton polygon plus Hensel lifting, first in the rational Hahn field and
then with the ramification bounded inside a power-series level.
-/
theorem puiseux_theorem {K : Type*} [Field K] [IsAlgClosed K]
    [CharZero K] :
    IsAlgClosed (HahnSeries Rat K) ∧
      (∃ (ι : LaurentSeries K →+* HahnSeries Rat K)
          (P : Subfield (HahnSeries Rat K))
          (hmem : ∀ y, ι y ∈ P)
          (e : ↥P ≃+* AlgebraicClosure (LaurentSeries K)),
          Function.Injective ι ∧
            (∀ x : ↥P, ∃ n : ℕ, 0 < n ∧
              ∀ r : Rat, HahnSeries.coeff (x : HahnSeries Rat K) r ≠ 0 →
                ∃ m : ℤ, r = (m : Rat) / (n : Rat)) ∧
            (∀ y : HahnSeries Rat K,
              (∃ n : ℕ, 0 < n ∧
                ∀ r : Rat, HahnSeries.coeff y r ≠ 0 →
                  ∃ m : ℤ, r = (m : Rat) / (n : Rat)) → y ∈ P) ∧
            (∀ y, e ⟨ι y, hmem y⟩ =
              algebraMap (LaurentSeries K)
                (AlgebraicClosure (LaurentSeries K)) y)) ∧
      Nonempty (LaurentSeries K ≃+* FractionRing (PowerSeries K)) := by
  refine ⟨HahnSeries.isAlgClosed_rat, ?_, puiseux_fractionRing_equiv⟩
  let ι : LaurentSeries K →+* HahnSeries Rat K := puiseux_laurentHom
  let P : Subfield (HahnSeries Rat K) := puiseuxSubfield K
  have hmem (y : LaurentSeries K) : ι y ∈ P := puiseux_laurentHom_mem y
  let _ : Algebra (LaurentSeries K) ↥P := puiseux_subfieldAlgebra
  let _ : IsAlgClosed ↥P := puiseux_subfield_isAlgClosed
  let _ : Algebra.IsAlgebraic (LaurentSeries K) ↥P :=
    puiseux_subfield_isAlgebraic
  let _ : IsAlgClosure (LaurentSeries K) ↥P :=
    { isAlgClosed := puiseux_subfield_isAlgClosed
      isAlgebraic := puiseux_subfield_isAlgebraic }
  let ea : ↥P ≃ₐ[LaurentSeries K] AlgebraicClosure (LaurentSeries K) :=
    IsAlgClosure.equiv (LaurentSeries K) ↥P
      (AlgebraicClosure (LaurentSeries K))
  let e : ↥P ≃+* AlgebraicClosure (LaurentSeries K) := ea.toRingEquiv
  refine ⟨ι, P, hmem, e, puiseux_laurentHom_injective, ?_, ?_, ?_⟩
  · intro x
    exact x.property
  · intro y hy
    exact hy
  · intro y
    change ea ⟨ι y, hmem y⟩ =
      algebraMap (LaurentSeries K) (AlgebraicClosure (LaurentSeries K)) y
    exact ea.commutes y

end

end MetaMathlibExt
