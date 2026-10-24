import Mathlib
import sympy.Basic
import sympy.atlas.FieldTheory.PuiseuxTheorem
open Polynomial
open HahnSeries
open MetaMathlibExt


namespace MetaMathlibExt


namespace HahnSeries

/--
[isAlgClosed_rat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
lemma isAlgClosed_rat
  [Field K] [IsAlgClosed K] [CharZero K] :
-- imply
  IsAlgClosed (HahnSeries Rat K) :=
-- proof
  MetaMathlibExt.puiseux.hahnSeries_isAlgClosed
end
namespace MetaMathlibExt
noncomputable section
open Polynomial


/--
[puiseux_isPWO_biUnion_finset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_isPWO_biUnion_finset (s : ℕ → Set Rat) (u : Finset ℕ)
  (hs : ∀ n, (s n).IsPWO) : (⋃ n ∈ (u : Set ℕ), s n).IsPWO := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | @insert a u ha ih =>
    rw [show (⋃ n ∈ ((insert a u : Finset ℕ) : Set ℕ), s n) =
      s a ∪ ⋃ n ∈ (u : Set ℕ), s n by ext x; simp]
    exact (hs a).union ih

end MetaMathlibExt

namespace MetaMathlibExt

/--
[puiseux_isPWO_iUnion_of_linear_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_isPWO_iUnion_of_linear_lower_bound (d : Rat) (hd : 0 < d)
  (s : ℕ → Set Rat) (hs : ∀ n, (s n).IsPWO)
  (hlower : ∀ n q, q ∈ s n → (n : Rat) * d ≤ q) :
  (⋃ n, s n).IsPWO := by
  rw [Set.isPWO_iff_isWF, Set.isWF_iff_no_descending_seq]
  intro f hf hmem
  choose k hk using fun n ↦ Set.mem_iUnion.mp (hmem n)
  obtain ⟨B, hB⟩ := exists_nat_ge (f 0 / d)
  have hkB (n : ℕ) : k n ≤ B := by
    have hkdiv : (k n : Rat) ≤ f 0 / d :=
      (le_div_iff₀ hd).2 <| (hlower (k n) (f n) (hk n)).trans
        (hf.antitone (Nat.zero_le n))
    exact_mod_cast hkdiv.trans hB
  have hfinite := puiseux_isPWO_biUnion_finset s (Finset.range (B + 1)) hs
  have hsubset : ∀ n, f n ∈ ⋃ i ∈ ((Finset.range (B + 1) : Finset ℕ) : Set ℕ), s i := by
    intro n
    apply Set.mem_iUnion.mpr
    refine ⟨k n, Set.mem_iUnion.mpr ⟨?_, hk n⟩⟩
    simpa using Nat.lt_succ_iff.mpr (hkB n)
  have hwf := Set.isPWO_iff_isWF.mp hfinite
  exact (Set.isWF_iff_no_descending_seq.mp hwf f hf) hsubset

end MetaMathlibExt

namespace MetaMathlibExt

/--
[puiseux_coe_uniformizer_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_coe_uniformizer_pow {K : Type*} [Field K] (d : Rat)
  (hd : 0 < d) (n : ℕ) :
  (((puiseux_uniformizer (K := K) d hd) ^ n : puiseuxValuationRing K) :
    HahnSeries Rat K) = HahnSeries.single (n • d) 1 := by
  simp [puiseux_uniformizer, HahnSeries.single_pow]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[puiseux_mem_hahnIdeal_pow_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_mem_hahnIdeal_pow_iff {K : Type*} [Field K] (d : Rat)
  (hd : 0 < d) (n : ℕ) (x : puiseuxValuationRing K) :
  x ∈ puiseux_hahnIdeal (K := K) d hd ^ n ↔
    (n : Rat) * d ≤ (x : HahnSeries Rat K).orderTop := by
  rw [puiseux_hahnIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩
    change (n : Rat) * d ≤
      ((((puiseux_uniformizer (K := K) d hd) ^ n : puiseuxValuationRing K) :
        HahnSeries Rat K) * (y : HahnSeries Rat K)).orderTop
    rw [HahnSeries.orderTop_mul, puiseux_coe_uniformizer_pow,
      HahnSeries.orderTop_single one_ne_zero]
    simpa [nsmul_eq_mul, add_comm] using add_le_add_left
      (show 0 ≤ (y : HahnSeries Rat K).orderTop from by
        have hiff : (y : HahnSeries Rat K) ∈ (puiseux_hahnVal K).valuationSubring ↔
          0 ≤ (y : HahnSeries Rat K).orderTop := by
          rw [Valuation.mem_valuationSubring_iff]
          rfl
        exact hiff.mp y.property)
      ((n : Rat) * d : WithTop Rat)
  · intro hx
    let a : Rat := (n : Rat) * d
    let yF : HahnSeries Rat K := HahnSeries.single (-a) 1 * (x : HahnSeries Rat K)
    have hyorder : 0 ≤ yF.orderTop := by
      change 0 ≤ (HahnSeries.single (-a) (1 : K) * (x : HahnSeries Rat K)).orderTop
      rw [HahnSeries.orderTop_mul, HahnSeries.orderTop_single one_ne_zero]
      change (a : WithTop Rat) ≤ (x : HahnSeries Rat K).orderTop at hx
      calc
        (0 : WithTop Rat) = ((-a : Rat) : WithTop Rat) + (a : WithTop Rat) := by simp
        _ ≤ ((-a : Rat) : WithTop Rat) + (x : HahnSeries Rat K).orderTop :=
          add_le_add_right hx _
    let y : puiseuxValuationRing K := ⟨yF, by
      rw [show yF ∈ (puiseux_hahnVal K).valuationSubring ↔ 0 ≤ yF.orderTop by
        rw [Valuation.mem_valuationSubring_iff]
        rfl]
      exact hyorder⟩
    refine ⟨y, Subtype.ext ?_⟩
    change (x : HahnSeries Rat K) =
      (((puiseux_uniformizer (K := K) d hd) ^ n : puiseuxValuationRing K) :
        HahnSeries Rat K) * yF
    rw [puiseux_coe_uniformizer_pow]
    symm
    rw [show yF = HahnSeries.single (-a) (1 : K) * (x : HahnSeries Rat K) from rfl,
      ← mul_assoc, HahnSeries.single_mul_single]
    simp [a, nsmul_eq_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[puiseux_hahnIdeal_isAdicComplete](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_hahnIdeal_isAdicComplete {K : Type*} [Field K] (d : Rat)
  (hd : 0 < d) :
  IsAdicComplete (puiseux_hahnIdeal (K := K) d hd) (puiseuxValuationRing K) := by
  let I := puiseux_hahnIdeal (K := K) d hd
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    apply Subtype.ext
    change (x : HahnSeries Rat K) = 0
    by_contra hne
    have htop : (x : HahnSeries Rat K).orderTop ≠ ⊤ :=
      HahnSeries.orderTop_ne_top.mpr hne
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp htop
    obtain ⟨n, hn⟩ := exists_nat_gt (q / d)
    have hmem := hx n
    rw [SModEq.zero, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one,
      puiseux_mem_hahnIdeal_pow_iff] at hmem
    have hlt : q < (n : Rat) * d := (div_lt_iff₀ hd).mp hn
    rw [← hq] at hmem
    exact (not_le_of_gt hlt) (WithTop.coe_le_coe.mp hmem)
  · intro f hf
    have hdiff (n : ℕ) : (n : Rat) * d ≤
      (((f (n + 1) - f n : puiseuxValuationRing K) : HahnSeries Rat K).orderTop) := by
      have h := hf (m := n) (n := n + 1) (Nat.le_succ n)
      rw [SModEq.sub_mem, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at h
      have h' : f (n + 1) - f n ∈ I ^ n := by
        simpa only [neg_sub] using (I ^ n).neg_mem h
      exact (puiseux_mem_hahnIdeal_pow_iff d hd n _).mp h'
    let e : ℕ → HahnSeries Rat K := fun n ↦ f (n + 1) - f n
    have heorder (n : ℕ) : (n : Rat) * d ≤ (e n).orderTop := hdiff n
    let E : HahnSeries.SummableFamily Rat K ℕ :=
      { toFun := e
        isPWO_iUnion_support' := puiseux_isPWO_iUnion_of_linear_lower_bound d hd
          (fun n ↦ (e n).support) (fun n ↦ (e n).isPWO_support) fun n q hq ↦
            WithTop.coe_le_coe.mp <|
              (heorder n).trans (HahnSeries.orderTop_le_of_coeff_ne_zero hq)
        finite_co_support' := by
          intro q
          obtain ⟨B, hB⟩ := exists_nat_ge (q / d)
          apply (Set.finite_Iic B).subset
          intro n hn
          have hnq : (n : Rat) * d ≤ q := WithTop.coe_le_coe.mp <|
            (heorder n).trans (HahnSeries.orderTop_le_of_coeff_ne_zero hn)
          have hndiv : (n : Rat) ≤ q / d := (le_div_iff₀ hd).2 hnq
          exact_mod_cast hndiv.trans hB }
    have hsum_nonneg : 0 ≤ E.hsum.orderTop := by
      rw [HahnSeries.le_orderTop_iff_forall]
      intro q hq
      rw [HahnSeries.SummableFamily.coeff_hsum]
      apply finsum_eq_zero_of_forall_eq_zero
      intro n
      apply HahnSeries.coeff_eq_zero_of_lt_orderTop
      have hnd : (0 : Rat) ≤ (n : Rat) * d := mul_nonneg (by positivity) hd.le
      have hnd' : (0 : WithTop Rat) ≤ ((n : Rat) * d : Rat) := by exact_mod_cast hnd
      exact hq.trans_le (hnd'.trans (heorder n))
    let S : puiseuxValuationRing K := ⟨E.hsum, by
      rw [show E.hsum ∈ (puiseux_hahnVal K).valuationSubring ↔ 0 ≤ E.hsum.orderTop by
        rw [Valuation.mem_valuationSubring_iff]
        rfl]
      exact hsum_nonneg⟩
    refine ⟨f 0 + S, ?_⟩
    intro n
    rw [SModEq.sub_mem, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one,
      puiseux_mem_hahnIdeal_pow_iff]
    rw [HahnSeries.le_orderTop_iff_forall]
    intro q hq
    have hsupport : Function.support (fun i ↦ (e i).coeff q) ⊆ Finset.range n := by
      intro i hi
      simp only [Function.mem_support] at hi
      simp only [Finset.mem_coe, Finset.mem_range]
      by_contra hin
      have hni : n ≤ i := Nat.le_of_not_gt hin
      have hbound : (n : Rat) * d ≤ (i : Rat) * d := by gcongr
      have hbound' : (((n : Rat) * d : Rat) : WithTop Rat) ≤
        (((i : Rat) * d : Rat) : WithTop Rat) := by exact_mod_cast hbound
      have hcontra : (q : WithTop Rat) < (q : WithTop Rat) :=
        hq.trans_le (hbound'.trans <| (heorder i).trans
          (HahnSeries.orderTop_le_of_coeff_ne_zero hi))
      exact (lt_irrefl _ hcontra).elim
    change (f n : HahnSeries Rat K).coeff q -
      ((f 0 : HahnSeries Rat K).coeff q + E.hsum.coeff q) = 0
    rw [HahnSeries.SummableFamily.coeff_hsum]
    change (f n : HahnSeries Rat K).coeff q -
      ((f 0 : HahnSeries Rat K).coeff q + ∑ᶠ i, (e i).coeff q) = 0
    rw [finsum_eq_finsetSum_of_support_subset _ hsupport]
    have htelF := congrArg (ValuationSubring.subtype (puiseuxValuationRing K))
      (Finset.sum_range_sub f n)
    simp only [map_sum, map_sub] at htelF
    have htel := congrArg (fun z : HahnSeries Rat K ↦ z.coeff q) htelF
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_sub] at htel
    have htel' :
      (∑ i ∈ Finset.range n,
        ((f (i + 1) : HahnSeries Rat K).coeff q -
          (f i : HahnSeries Rat K).coeff q)) =
        (f n : HahnSeries Rat K).coeff q - (f 0 : HahnSeries Rat K).coeff q := by
      simpa only [ValuationSubring.subtype_apply] using htel
    change (f n : HahnSeries Rat K).coeff q -
      ((f 0 : HahnSeries Rat K).coeff q + ∑ i ∈ Finset.range n,
        ((f (i + 1) : HahnSeries Rat K).coeff q -
          (f i : HahnSeries Rat K).coeff q)) = 0
    rw [htel']
    ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[puiseux_tail_coeff_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_tail_coeff_zero {K : Type*} [Field K]
  (x : puiseuxValuationRing K) :
  ((puiseux_tail x : puiseuxValuationRing K) : HahnSeries Rat K).coeff 0 = 0 := by
  simp [puiseux_tail, puiseux_constants, HahnSeries.C_apply]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[puiseux_tail_orderTop_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_tail_orderTop_pos {K : Type*} [Field K]
  (x : puiseuxValuationRing K) :
  (0 : WithTop Rat) <
    ((puiseux_tail x : puiseuxValuationRing K) : HahnSeries Rat K).orderTop := by
  have hnonneg : (0 : WithTop Rat) ≤
    ((puiseux_tail x : puiseuxValuationRing K) : HahnSeries Rat K).orderTop := by
    have hiff :
      ((puiseux_tail x : puiseuxValuationRing K) : HahnSeries Rat K) ∈
        (puiseux_hahnVal K).valuationSubring ↔
        0 ≤ ((puiseux_tail x : puiseuxValuationRing K) :
          HahnSeries Rat K).orderTop := by
      rw [Valuation.mem_valuationSubring_iff]
      rfl
    exact hiff.mp (puiseux_tail x).property
  exact lt_of_le_of_ne hnonneg
    (HahnSeries.orderTop_ne_of_coeff_eq_zero (puiseux_tail_coeff_zero x)).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[puiseux_epsilon_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_epsilon_pos {K : Type*} [Field K]
  (x : puiseuxValuationRing K) : 0 < puiseux_epsilon x := by
  by_cases hx : puiseux_tail x = 0
  · simp [puiseux_epsilon, hx]
  · simp only [puiseux_epsilon, hx, reduceIte]
    have hx' : ((puiseux_tail x : puiseuxValuationRing K) :
      HahnSeries Rat K) ≠ 0 := by
      intro h
      apply hx
      exact Subtype.ext h
    exact (HahnSeries.zero_lt_orderTop_iff hx').mp
      (puiseux_tail_orderTop_pos x)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[puiseux_precision_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_precision_pos {K : Type*} [Field K]
  (p : (puiseuxValuationRing K)[X]) : 0 < puiseux_precision p := by
  let s := insert 1 (p.support.image fun i ↦ puiseux_epsilon (p.coeff i))
  have hmem := s.min'_mem (by simp [s])
  change 0 < s.min' _
  obtain h | h := Finset.mem_insert.mp hmem
  · rw [h]
    norm_num
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    rw [← hi]
    exact puiseux_epsilon_pos (p.coeff i)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[puiseux_precision_le_epsilon](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_precision_le_epsilon {K : Type*} [Field K]
  (p : (puiseuxValuationRing K)[X]) (i : ℕ) :
  puiseux_precision p ≤ puiseux_epsilon (p.coeff i) := by
  rw [puiseux_precision]
  by_cases hi : i ∈ p.support
  · apply Finset.min'_le
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  · have hcoeff : p.coeff i = 0 := Polynomial.notMem_support_iff.mp hi
    rw [hcoeff]
    have htail : puiseux_tail (0 : puiseuxValuationRing K) = 0 := by
      simp [puiseux_tail]
    simp only [puiseux_epsilon, htail, reduceIte]
    exact Finset.min'_le _ _ (Finset.mem_insert_self 1 _)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[puiseux_tail_mem_precision_ideal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_tail_mem_precision_ideal {K : Type*} [Field K]
  (p : (puiseuxValuationRing K)[X]) (i : ℕ) :
  puiseux_tail (p.coeff i) ∈
    puiseux_hahnIdeal (K := K) (puiseux_precision p) (puiseux_precision_pos p) := by
  rw [show puiseux_hahnIdeal (K := K) (puiseux_precision p)
    (puiseux_precision_pos p) =
    puiseux_hahnIdeal (K := K) (puiseux_precision p)
      (puiseux_precision_pos p) ^ 1 by simp]
  rw [puiseux_mem_hahnIdeal_pow_iff]
  simp only [Nat.cast_one]
  by_cases htail : puiseux_tail (p.coeff i) = 0
  · simp [htail]
  · have hle := puiseux_precision_le_epsilon p i
    simp only [puiseux_epsilon, htail, reduceIte] at hle
    have htail' : ((puiseux_tail (p.coeff i) : puiseuxValuationRing K) :
      HahnSeries Rat K) ≠ 0 := by
      intro h
      apply htail
      exact Subtype.ext h
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero htail']
    exact_mod_cast (show 1 * puiseux_precision p ≤
      ((puiseux_tail (p.coeff i) : puiseuxValuationRing K) :
        HahnSeries Rat K).order by simpa using hle)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[puiseux_sub_constants_eq_tail](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_sub_constants_eq_tail {K : Type*} [Field K]
  (x : puiseuxValuationRing K) :
  x - puiseux_constants (puiseux_residueHom x) = puiseux_tail x := by
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[puiseux_map_quotient_eq_map_residuePolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_map_quotient_eq_map_residuePolynomial {K : Type*}
  [Field K] (p : (puiseuxValuationRing K)[X]) :
  let I := puiseux_hahnIdeal (K := K) (puiseux_precision p)
    (puiseux_precision_pos p)
  p.map (Ideal.Quotient.mk I) =
    (puiseux_residuePolynomial p).map
      ((Ideal.Quotient.mk I).comp puiseux_constants) := by
  let I := puiseux_hahnIdeal (K := K) (puiseux_precision p)
    (puiseux_precision_pos p)
  ext i
  simp only [Polynomial.coeff_map, puiseux_residuePolynomial, RingHom.comp_apply]
  apply (Ideal.Quotient.eq (I := I)).mpr
  rw [puiseux_sub_constants_eq_tail]
  exact puiseux_tail_mem_precision_ideal p i

end MetaMathlibExt

namespace MetaMathlibExt

/--
[puiseux_hahnIdeal_ne_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_hahnIdeal_ne_top {K : Type*} [Field K]
  (d : Rat) (hd : 0 < d) : puiseux_hahnIdeal (K := K) d hd ≠ ⊤ := by
  intro htop
  have hmem : (1 : puiseuxValuationRing K) ∈
    puiseux_hahnIdeal (K := K) d hd ^ 1 := by
    rw [pow_one, htop]
    simp
  have hle := (puiseux_mem_hahnIdeal_pow_iff d hd 1 1).mp hmem
  norm_num at hle
  exact (not_le_of_gt hd) hle

end MetaMathlibExt

namespace MetaMathlibExt

/--
[puiseux_lift_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_lift_factorization {K : Type*} [Field K]
  (p : (puiseuxValuationRing K)[X]) (hp : p.Monic) (g h : K[X])
  (hg : g.Monic) (hh : h.Monic)
  (hfac : puiseux_residuePolynomial p = g * h) (hcop : IsCoprime g h) :
  ∃ G H : (puiseuxValuationRing K)[X],
    G.Monic ∧ H.Monic ∧ p = G * H ∧
      G.natDegree = g.natDegree ∧ H.natDegree = h.natDegree := by
  let d := puiseux_precision p
  have hd : 0 < d := puiseux_precision_pos p
  let I := puiseux_hahnIdeal (K := K) d hd
  let φ : K →+* puiseuxValuationRing K ⧸ I :=
    (Ideal.Quotient.mk I).comp puiseux_constants
  let gbar : (puiseuxValuationRing K ⧸ I)[X] := g.map φ
  let hbar : (puiseuxValuationRing K ⧸ I)[X] := h.map φ
  let _ : IsAdicComplete I (puiseuxValuationRing K) :=
    puiseux_hahnIdeal_isAdicComplete d hd
  let _ : Nontrivial (puiseuxValuationRing K ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr <| by
      simpa [I] using puiseux_hahnIdeal_ne_top (K := K) d hd
  have hgbar : gbar.Monic := hg.map φ
  have hhbar : hbar.Monic := hh.map φ
  have hfacbar : p.map (Ideal.Quotient.mk I) = gbar * hbar := by
    rw [show p.map (Ideal.Quotient.mk I) =
      (puiseux_residuePolynomial p).map φ by
      exact puiseux_map_quotient_eq_map_residuePolynomial p]
    rw [hfac]
    simp [gbar, hbar]
  have hcopbar : IsCoprime gbar hbar := by
    obtain ⟨a, b, hab⟩ := hcop
    refine ⟨a.map φ, b.map φ, ?_⟩
    simpa [gbar, hbar] using congrArg (Polynomial.map φ) hab
  obtain ⟨G, H, hG, hH, hpGH, _, _, hGdeg, hHdeg⟩ :=
    Polynomial.exists_monic_coprime_factorization_of_isAdicComplete_natDegree
      I p hp gbar hbar hgbar hhbar hfacbar hcopbar
  refine ⟨G, H, hG, hH, hpGH, ?_, ?_⟩
  · rw [hGdeg]
    change (g.map φ).natDegree = g.natDegree
    exact Polynomial.natDegree_map_eq_of_injective φ.injective g
  · rw [hHdeg]
    change (h.map φ).natDegree = h.natDegree
    exact Polynomial.natDegree_map_eq_of_injective φ.injective h

end MetaMathlibExt

namespace MetaMathlibExt.puiseux

/--
[coeff_newtonPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma coeff_newtonPolynomial {K : Type*} [Field K]
  (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
  (hpow : f ≠ X ^ f.natDegree) (i : ℕ) (hi : i ≤ f.natDegree) :
  (newtonPolynomial f hf hpow).coeff i =
    integralScaledCoeff f hf hpow ⟨i, Nat.lt_succ_of_le hi⟩ := by
  classical
  simpa [newtonPolynomial] using
    Polynomial.ofFn_coeff_eq_val_of_lt
      (integralScaledCoeff f hf hpow) (Nat.lt_succ_of_le hi)

end MetaMathlibExt.puiseux

namespace MetaMathlibExt.puiseux

/--
[coe_coeff_newtonPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma coe_coeff_newtonPolynomial {K : Type*} [Field K]
  (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
  (hpow : f ≠ X ^ f.natDegree) (i : ℕ) (hi : i ≤ f.natDegree) :
  (((newtonPolynomial f hf hpow).coeff i : O K) : HahnSeries Rat K) =
    scaledCoeff f (newtonSlope f hf hpow) i := by
  rw [coeff_newtonPolynomial f hf hpow i hi]
  rfl

end MetaMathlibExt.puiseux

namespace MetaMathlibExt.puiseux

/--
[newtonPolynomial_natDegree_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma newtonPolynomial_natDegree_le {K : Type*} [Field K]
  (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
  (hpow : f ≠ X ^ f.natDegree) :
  (newtonPolynomial f hf hpow).natDegree ≤ f.natDegree := by
  classical
  have hlt : (newtonPolynomial f hf hpow).natDegree < f.natDegree + 1 := by
    simpa [newtonPolynomial] using
      Polynomial.ofFn_natDegree_lt (R := O K)
        (n := f.natDegree + 1) (by omega)
        (integralScaledCoeff f hf hpow)
  exact Nat.lt_succ_iff.mp hlt

end MetaMathlibExt.puiseux

namespace MetaMathlibExt.puiseux

/--
[newtonPolynomial_coeff_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma newtonPolynomial_coeff_natDegree {K : Type*} [Field K]
  (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
  (hpow : f ≠ X ^ f.natDegree) :
  (newtonPolynomial f hf hpow).coeff f.natDegree = 1 := by
  apply Subtype.ext
  rw [coe_coeff_newtonPolynomial f hf hpow f.natDegree le_rfl]
  simp [scaledCoeff, hf.coeff_natDegree]

end MetaMathlibExt.puiseux

namespace MetaMathlibExt.puiseux

/--
[newtonPolynomial_monic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma newtonPolynomial_monic {K : Type*} [Field K]
  (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
  (hpow : f ≠ X ^ f.natDegree) : (newtonPolynomial f hf hpow).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one f.natDegree
    (newtonPolynomial_natDegree_le f hf hpow)
    (newtonPolynomial_coeff_natDegree f hf hpow)

end MetaMathlibExt.puiseux

namespace MetaMathlibExt.puiseux

/--
[newtonPolynomial_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma newtonPolynomial_natDegree {K : Type*} [Field K]
  (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
  (hpow : f ≠ X ^ f.natDegree) :
  (newtonPolynomial f hf hpow).natDegree = f.natDegree := by
  apply Nat.le_antisymm (newtonPolynomial_natDegree_le f hf hpow)
  apply Polynomial.le_natDegree_of_ne_zero
  rwa [newtonPolynomial_coeff_natDegree f hf hpow]

end MetaMathlibExt.puiseux

namespace MetaMathlibExt.puiseux

/--
[newtonPolynomial_nextCoeff_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma newtonPolynomial_nextCoeff_eq_zero {K : Type*} [Field K]
  (f : (HahnSeries Rat K)[X]) (hf : f.Monic) (hn : 0 < f.natDegree)
  (hnext : f.nextCoeff = 0) (hpow : f ≠ X ^ f.natDegree) :
  (newtonPolynomial f hf hpow).nextCoeff = 0 := by
  have hpdeg := newtonPolynomial_natDegree f hf hpow
  rw [nextCoeff_of_natDegree_pos (hpdeg.symm ▸ hn), hpdeg]
  have hpred : f.natDegree - 1 ≤ f.natDegree := Nat.sub_le _ _
  apply Subtype.ext
  rw [coe_coeff_newtonPolynomial f hf hpow (f.natDegree - 1) hpred]
  have hcoeff : f.coeff (f.natDegree - 1) = 0 := by
    rwa [← nextCoeff_of_natDegree_pos hn]
  simp [scaledCoeff, hcoeff]

end MetaMathlibExt.puiseux

namespace MetaMathlibExt.puiseux

/--
[residuePolynomial_monic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma residuePolynomial_monic {K : Type*} [Field K]
  (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
  (hpow : f ≠ X ^ f.natDegree) :
  (puiseux_residuePolynomial (newtonPolynomial f hf hpow)).Monic :=
  (newtonPolynomial_monic f hf hpow).map puiseux_residueHom

end MetaMathlibExt.puiseux

namespace MetaMathlibExt.puiseux

/--
[residuePolynomial_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma residuePolynomial_natDegree {K : Type*} [Field K]
  (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
  (hpow : f ≠ X ^ f.natDegree) :
  (puiseux_residuePolynomial (newtonPolynomial f hf hpow)).natDegree =
    f.natDegree := by
  rw [puiseux_residuePolynomial,
    (newtonPolynomial_monic f hf hpow).natDegree_map puiseux_residueHom,
    newtonPolynomial_natDegree]

end MetaMathlibExt.puiseux

namespace MetaMathlibExt.puiseux

/--
[residuePolynomial_nextCoeff_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma residuePolynomial_nextCoeff_eq_zero {K : Type*} [Field K]
  (f : (HahnSeries Rat K)[X]) (hf : f.Monic) (hn : 0 < f.natDegree)
  (hnext : f.nextCoeff = 0) (hpow : f ≠ X ^ f.natDegree) :
  (puiseux_residuePolynomial (newtonPolynomial f hf hpow)).nextCoeff = 0 := by
  have hunit : IsUnit (newtonPolynomial f hf hpow).leadingCoeff := by
    rwa [(newtonPolynomial_monic f hf hpow).leadingCoeff]
  rw [puiseux_residuePolynomial,
    Polynomial.nextCoeff_map_eq_of_isUnit_leadingCoeff puiseux_residueHom hunit,
    newtonPolynomial_nextCoeff_eq_zero f hf hn hnext hpow, map_zero]

end MetaMathlibExt.puiseux

namespace MetaMathlibExt.puiseux

/--
[scaledCoeff_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma scaledCoeff_eq {K : Type*} [Field K]
  (f : (HahnSeries Rat K)[X]) (s : Rat) (i : ℕ) :
  scaledCoeff f s i =
    HahnSeries.single (-((f.natDegree : Rat) * s)) 1 *
      (f.coeff i * (HahnSeries.single s 1) ^ i) := by
  rw [scaledCoeff]
  calc
    HahnSeries.single (((i : Rat) - (f.natDegree : Rat)) * s) 1 * f.coeff i =
      (HahnSeries.single (-((f.natDegree : Rat) * s)) 1 *
        HahnSeries.single ((i : Rat) * s) 1) * f.coeff i := by
      rw [HahnSeries.single_mul_single, one_mul]
      apply congrArg (fun q : Rat ↦ HahnSeries.single q 1 * f.coeff i)
      ring
    _ = HahnSeries.single (-((f.natDegree : Rat) * s)) 1 *
      (f.coeff i * HahnSeries.single ((i : Rat) * s) 1) := by
      ac_rfl
    _ = HahnSeries.single (-((f.natDegree : Rat) * s)) 1 *
      (f.coeff i * (HahnSeries.single s 1) ^ i) := by
      rw [HahnSeries.single_pow]
      simp [nsmul_eq_mul]

end MetaMathlibExt.puiseux

namespace MetaMathlibExt.puiseux

/--
[map_newtonPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma map_newtonPolynomial {K : Type*} [Field K]
  (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
  (hpow : f ≠ X ^ f.natDegree) :
  (newtonPolynomial f hf hpow).map
    (ValuationSubring.subtype (O K)) =
    C (HahnSeries.single
      (-((f.natDegree : Rat) * newtonSlope f hf hpow)) 1) *
      f.comp (C (HahnSeries.single (newtonSlope f hf hpow) 1) * X) := by
  apply Polynomial.ext
  intro i
  rw [Polynomial.coeff_map, Polynomial.coeff_C_mul,
    Polynomial.comp_C_mul_X_coeff]
  by_cases hi : i ≤ f.natDegree
  · change (((newtonPolynomial f hf hpow).coeff i : O K) :
    HahnSeries Rat K) = _
    rw [coe_coeff_newtonPolynomial f hf hpow i hi]
    exact scaledCoeff_eq f (newtonSlope f hf hpow) i
  · have hlt : f.natDegree < i := Nat.lt_of_not_ge hi
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt <|
      (newtonPolynomial_natDegree f hf hpow).symm ▸ hlt]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    simp

end MetaMathlibExt.puiseux

namespace MetaMathlibExt.puiseux

/--
[root_of_root_newtonPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma root_of_root_newtonPolynomial {K : Type*} [Field K]
  (f : (HahnSeries Rat K)[X]) (hf : f.Monic)
  (hpow : f ≠ X ^ f.natDegree) {x : HahnSeries Rat K}
  (hx : ((newtonPolynomial f hf hpow).map
    (ValuationSubring.subtype (O K))).IsRoot x) :
  f.IsRoot (HahnSeries.single (newtonSlope f hf hpow) 1 * x) := by
  rw [Polynomial.IsRoot] at hx ⊢
  rw [map_newtonPolynomial f hf hpow, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X] at hx
  obtain hscale | hroot := mul_eq_zero.mp hx
  · exact (HahnSeries.single_ne_zero one_ne_zero hscale).elim
  · exact hroot

end MetaMathlibExt.puiseux

namespace MetaMathlibExt.puiseux

/--
[nextCoeff_comp_X_add_C](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma nextCoeff_comp_X_add_C {L : Type*} [Field L]
  (p : L[X]) (hp : p.Monic) (hn : 0 < p.natDegree) (c : L) :
  (p.comp (X + C c)).nextCoeff = p.nextCoeff + p.natDegree • c := by
  let n := p.natDegree
  have hn' : 0 < n := hn
  have hcompdeg : (p.comp (X + C c)).natDegree = n := by
    change (p.taylor c).natDegree = n
    simp [n]
  rw [nextCoeff_of_natDegree_pos (hcompdeg ▸ hn')]
  rw [hcompdeg]
  change (p.taylor c).coeff (n - 1) = _
  rw [Polynomial.taylor_coeff]
  have hhasse : p.hasseDeriv (n - 1) =
    C p.nextCoeff + C (n : L) * X := by
    ext k
    by_cases hk0 : k = 0
    · subst k
      rw [Polynomial.hasseDeriv_coeff]
      simp [n, nextCoeff_of_natDegree_pos hn]
    by_cases hk1 : k = 1
    · subst k
      rw [Polynomial.hasseDeriv_coeff]
      have hsum : 1 + (n - 1) = n := by omega
      rw [hsum, coeff_natDegree, hp.leadingCoeff]
      have hchoose : n.choose (n - 1) = n := by
        rw [Nat.choose_symm (by omega), Nat.choose_one_right]
      simp [hchoose]
    · rw [Polynomial.hasseDeriv_coeff]
      have hk2 : 2 ≤ k := by omega
      have hlt : n < k + (n - 1) := by omega
      rw [coeff_eq_zero_of_natDegree_lt (by simpa [n] using hlt)]
      rw [coeff_add, coeff_C_of_ne_zero hk0, coeff_C_mul_X]
      simp [hk1]
  rw [hhasse]
  simp [nsmul_eq_mul, mul_comm, n]

end MetaMathlibExt.puiseux

namespace MetaMathlibExt.puiseux

/--
[split_residue](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma split_residue {K : Type*} [Field K] [IsAlgClosed K]
  [CharZero K] (r : K[X]) (n : ℕ) (hr : r.Monic) (hn : 0 < n)
  (hrdeg : r.natDegree = n) (hrnext : r.nextCoeff = 0)
  (hrpow : r ≠ X ^ n) :
  ∃ g h : K[X], g.Monic ∧ h.Monic ∧ r = g * h ∧ IsCoprime g h ∧
    0 < g.natDegree ∧ g.natDegree < n ∧
    0 < h.natDegree ∧ h.natDegree < n := by
  have hr0 : r ≠ 0 := hr.ne_zero
  have hrnatpos : 0 < r.natDegree := hrdeg.symm ▸ hn
  have hrdegree : r.degree ≠ 0 :=
    (Polynomial.natDegree_pos_iff_degree_pos.mp hrnatpos).ne'
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root r hrdegree
  let m := r.rootMultiplicity a
  let g : K[X] := (X - C a) ^ m
  let h : K[X] := r /ₘ g
  have hmpos : 0 < m := (Polynomial.rootMultiplicity_pos hr0).mpr ha
  have hg : g.Monic := (monic_X_sub_C a).pow m
  have hfac' : g * h = r := by
    exact Polynomial.pow_mul_divByMonic_rootMultiplicity_eq r a
  have hh : h.Monic := hg.of_mul_monic_left (hfac' ▸ hr)
  have hgdeg : g.natDegree = m := by simp [g]
  have hsumdeg : m + h.natDegree = n := by
    rw [← hgdeg, ← (hg.natDegree_mul hh), hfac', hrdeg]
  have hmlt : m < n := by
    have hmle : m ≤ n := by omega
    apply lt_of_le_of_ne hmle
    intro hmn
    have hhdeg : h.natDegree = 0 := by omega
    have hh1 : h = 1 := Polynomial.eq_one_of_monic_natDegree_zero hh hhdeg
    have hr_eq_g : r = g := by simpa [hh1] using hfac'.symm
    have hnextg : g.nextCoeff = 0 := hr_eq_g ▸ hrnext
    have hna : n • (-a) = 0 := by
      rw [show n = m by omega, ← Polynomial.nextCoeff_X_sub_C a,
        ← (monic_X_sub_C a).nextCoeff_pow]
      exact hnextg
    have ha0 : a = 0 := by
      rw [nsmul_eq_mul] at hna
      have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      obtain h | h := mul_eq_zero.mp hna
      · exact (hnK h).elim
      · exact neg_eq_zero.mp h
    apply hrpow
    rw [hr_eq_g]
    change (X - C a) ^ m = X ^ n
    rw [show m = n by omega, ha0]
    simp
  have hhpos : 0 < h.natDegree := by omega
  have hh_lt : h.natDegree < n := by omega
  have hndvd : ¬ (X - C a) ∣ h := by
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
    exact Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero a hr0
  have hcoplin : IsCoprime (X - C a) h :=
    (Polynomial.prime_X_sub_C a).coprime_iff_not_dvd.mpr hndvd
  have hcop : IsCoprime g h := hcoplin.pow_left
  refine ⟨g, h, hg, hh, hfac'.symm, hcop, ?_, ?_, hhpos, hh_lt⟩
  · rw [hgdeg]
    exact hmpos
  · rw [hgdeg]
    exact hmlt

end MetaMathlibExt.puiseux

namespace MetaMathlibExt.puiseux

/--
[depressed_monic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma depressed_monic {L : Type*} [Field L]
  (f : L[X]) (hf : f.Monic) : (depressed f).Monic :=
  hf.comp_X_add_C (center f)

end MetaMathlibExt.puiseux

namespace MetaMathlibExt.puiseux

/--
[depressed_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma depressed_natDegree {L : Type*} [Field L] (f : L[X]) :
  (depressed f).natDegree = f.natDegree := by
  change (f.taylor (center f)).natDegree = f.natDegree
  simp

end MetaMathlibExt.puiseux

namespace MetaMathlibExt.puiseux

/--
[depressed_nextCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma depressed_nextCoeff {L : Type*} [Field L] [CharZero L]
  (f : L[X]) (hf : f.Monic) (hn : 0 < f.natDegree) :
  (depressed f).nextCoeff = 0 := by
  rw [depressed, nextCoeff_comp_X_add_C f hf hn, center]
  rw [nsmul_eq_mul]
  field_simp [Nat.cast_ne_zero.mpr hn.ne']
  ring

end MetaMathlibExt.puiseux

namespace MetaMathlibExt.puiseux

/--
[root_of_root_depressed](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma root_of_root_depressed {L : Type*} [Field L]
  (f : L[X]) {x : L} (hx : (depressed f).IsRoot x) :
  f.IsRoot (x + center f) := by
  rw [depressed, Polynomial.IsRoot, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at hx
  exact hx

end MetaMathlibExt.puiseux

namespace MetaMathlibExt

/--
[puiseux_fractionRing_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_fractionRing_equiv {K : Type*} [Field K] :
  Nonempty (LaurentSeries K ≃+* FractionRing (PowerSeries K)) :=
  ⟨(FractionRing.algEquiv (PowerSeries K) (LaurentSeries K)).symm.toRingEquiv⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[puiseux_levelHom_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_levelHom_injective {K : Type*} [Field K] {n : ℕ} (hn : 0 < n) :
  Function.Injective (puiseux_levelHom (K := K) n hn) :=
  RingHom.injective _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[puiseux_bounded_single](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_bounded_single {K : Type*} [Field K]
  (r : Rat) (a : K) : puiseuxBounded (HahnSeries.single r a) := by
  refine ⟨r.den, r.den_pos, ?_⟩
  intro s hs
  have hsr : s = r := by
    by_contra hne
    rw [HahnSeries.coeff_single_of_ne hne] at hs
    exact hs rfl
  subst s
  exact ⟨r.num, (Rat.num_div_den r).symm⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[puiseux_map_subfieldPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_map_subfieldPolynomial {K : Type*} [Field K]
  (f : (HahnSeries Rat K)[X]) (hf : puiseuxPolynomialBounded f) :
  (puiseux_subfieldPolynomial f hf).map (puiseuxSubfield K).subtype = f := by
  classical
  apply Polynomial.ext
  intro i
  rw [Polynomial.coeff_map]
  by_cases hi : i ≤ f.natDegree
  · rw [show (puiseux_subfieldPolynomial f hf).coeff i =
    ⟨f.coeff i, hf i⟩ by
    simpa [puiseux_subfieldPolynomial] using
      Polynomial.ofFn_coeff_eq_val_of_lt
        (fun j : Fin (f.natDegree + 1) ↦
          (⟨f.coeff j, hf j⟩ : ↥(puiseuxSubfield K)))
        (Nat.lt_succ_of_le hi)]
    rfl
  · have hlt : f.natDegree < i := Nat.lt_of_not_ge hi
    rw [show (puiseux_subfieldPolynomial f hf).coeff i = 0 by
      simpa [puiseux_subfieldPolynomial] using
        Polynomial.ofFn_coeff_eq_zero_of_ge
          (fun j : Fin (f.natDegree + 1) ↦
            (⟨f.coeff j, hf j⟩ : ↥(puiseuxSubfield K)))
          (Nat.succ_le_iff.mpr hlt)]
    rw [map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt hlt]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[puiseux_polynomialBounded_of_eq_map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_polynomialBounded_of_eq_map {K : Type*} [Field K]
  (q : (↥(puiseuxSubfield K))[X]) (f : (HahnSeries Rat K)[X])
  (h : q.map (puiseuxSubfield K).subtype = f) :
  puiseuxPolynomialBounded f := by
  intro i
  have hi := congrArg (fun p ↦ p.coeff i) h
  simp only [Polynomial.coeff_map] at hi
  rw [← hi]
  exact (q.coeff i).property

end MetaMathlibExt

namespace MetaMathlibExt

/--
[puiseux_powerSeriesLevelHom_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_powerSeriesLevelHom_injective {K : Type*} [Field K]
  {n : ℕ} (hn : 0 < n) :
  Function.Injective (puiseux_powerSeriesLevelHom (K := K) n hn) :=
  (puiseux_levelHom_injective hn).comp HahnSeries.ofPowerSeries_injective

end MetaMathlibExt

namespace MetaMathlibExt

/--
[puiseux_powerSeriesToValuationRing_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_powerSeriesToValuationRing_injective
  {K : Type*} [Field K] {n : ℕ} (hn : 0 < n) :
  Function.Injective (puiseux_powerSeriesToValuationRing (K := K) n hn) := by
  intro x y hxy
  apply puiseux_powerSeriesLevelHom_injective hn
  exact congrArg Subtype.val hxy

end MetaMathlibExt

namespace MetaMathlibExt

/--
[puiseux_map_powerSeries_quotient_eq_map_constantCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_map_powerSeries_quotient_eq_map_constantCoeff
  {K : Type*} [Field K] (q : (PowerSeries K)[X]) :
  let I : Ideal (PowerSeries K) := Ideal.span {PowerSeries.X}
  q.map (Ideal.Quotient.mk I) =
    (q.map PowerSeries.constantCoeff).map
      ((Ideal.Quotient.mk I).comp PowerSeries.C) := by
  let I : Ideal (PowerSeries K) := Ideal.span {PowerSeries.X}
  apply Polynomial.ext
  intro i
  simp only [Polynomial.coeff_map, RingHom.comp_apply]
  apply (Ideal.Quotient.eq (I := I)).mpr
  rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[puiseux_laurentHom_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_laurentHom_injective {K : Type*} [Field K] :
  Function.Injective (puiseux_laurentHom (K := K)) :=
  puiseux_levelHom_injective (by norm_num)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[puiseux_coeff_residuePart](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_coeff_residuePart {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
  (r : Fin n) (x : LaurentSeries K) (q : ℤ) :
  (puiseux_residuePart hn r x).coeff q =
    x.coeff ((n : ℤ) * q + (r : ℕ)) :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[puiseux_remainderFin_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_remainderFin_val {n : ℕ} (hn : 0 < n) (m : ℤ) :
  ((puiseux_remainderFin n hn m : ℕ) : ℤ) = m % (n : ℤ) :=
Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hn.ne'))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[puiseux_residue_eq_remainder_of_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_residue_eq_remainder_of_eq {n : ℕ} (hn : 0 < n) (m q : ℤ)
  (r : Fin n) (h : (n : ℤ) * q + (r : ℕ) = m) :
  r = puiseux_remainderFin n hn m := by
  have hdiv := (Int.ediv_emod_unique (a := m) (b := (n : ℤ)) (r := (r : ℕ)) (q := q)
    (by exact_mod_cast hn : (0 : ℤ) < n)).2
    ⟨by simpa [add_comm] using h, by positivity, by exact_mod_cast r.isLt⟩
  apply Fin.ext
  exact_mod_cast hdiv.2.symm.trans (puiseux_remainderFin_val hn m).symm

end MetaMathlibExt

/--
[puiseux_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_theorem_eq
  [Field K] [IsAlgClosed K] [CharZero K] :
-- imply
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
-- proof
  apply MetaMathlibExt.puiseux_theorem


-- created on 2026-10-20
-- updated on 2026-10-23
