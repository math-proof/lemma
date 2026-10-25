import Mathlib
import sympy.Basic
import Lemma.Scheme.IsCurveOver
import Lemma.Int.P2MUtil


namespace Definitions
end Definitions
open Definitions
open Int


/--
[AlgebraicCurve_CartierB_linearIndependent_of_cartier_fixed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_CartierB_linearIndependent_of_cartier_fixed.lean)
-/

private lemma exists_natCast_eq_of_pow_char_eq {K : Type*} [Field K] (p : ℕ)
  [Fact p.Prime] [CharP K p] {x : K} (hx : x ^ p = x) : ∃ m : ℕ, (m : K) = x := by
  have : ExpChar K p := .prime Fact.out
  classical
  by_contra hcon
  push Not at hcon
  have hcast : ∀ m : ℕ, (m : K) ^ p = (m : K) := by
    intro m
    induction m with
    | zero => rw [Nat.cast_zero, zero_pow ((Fact.out : p.Prime).pos.ne')]
    | succ k ih => rw [Nat.cast_succ, add_pow_char, ih, one_pow]
  have hlt : (Polynomial.X : Polynomial K).natDegree < (Polynomial.X ^ p : Polynomial K).natDegree := by
    rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]
    exact (Fact.out : p.Prime).one_lt
  have hdeg : (Polynomial.X ^ p - Polynomial.X : Polynomial K).natDegree = p := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]
  have hq0 : (Polynomial.X ^ p - Polynomial.X : Polynomial K) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    exact (Fact.out : p.Prime).pos.ne' hdeg.symm
  have hroot : ∀ y : K, y ^ p = y →
      y ∈ (Polynomial.X ^ p - Polynomial.X : Polynomial K).roots := by
    intro y hy
    rw [Polynomial.mem_roots']
    exact ⟨hq0, by simp [Polynomial.IsRoot, hy]⟩
  have hxS : x ∉ (Finset.range p).image (Nat.cast : ℕ → K) := by
    simp only [Finset.mem_image, Finset.mem_range]
    rintro ⟨m, -, hm⟩
    exact hcon m hm
  have himg : ((Finset.range p).image (Nat.cast : ℕ → K)).card = p := by
    rw [Finset.card_image_of_injOn
      (by rw [Finset.coe_range]; exact CharP.natCast_injOn_Iio K p), Finset.card_range]
  have hcard : (insert x ((Finset.range p).image (Nat.cast : ℕ → K))).card = p + 1 := by
    rw [Finset.card_insert_of_notMem hxS, himg]
  have hsub : insert x ((Finset.range p).image (Nat.cast : ℕ → K))
    ⊆ (Polynomial.X ^ p - Polynomial.X : Polynomial K).roots.toFinset := by
    intro y hy
    rw [Multiset.mem_toFinset]
    obtain rfl | hy := Finset.mem_insert.mp hy
    · exact hroot y hx
    ·
      obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hy
      exact hroot _ (hcast m)
  have hle : (insert x ((Finset.range p).image (Nat.cast : ℕ → K))).card ≤ p :=
    ((Finset.card_le_card hsub).trans (Multiset.toFinset_card_le _)).trans
      ((Polynomial.card_roots' _).trans_eq hdeg)
  rw [hcard] at hle
  exact absurd hle (by omega)

@[path]
private lemma main
  [Field K] [Field F] [Algebra K F] [AlgebraicCurve.IsCurveOver K F] [PerfectField K]
  {p : ℕ} [Fact p.Prime] [CharP K p]
  {C : Ω[F⁄K] →+ Ω[F⁄K]}
  {n : ℕ}
  {w : Fin n → Ω[F⁄K]}
-- given
  (hsemi : ∀ (f : F) (η : Ω[F⁄K]), C (f ^ p • η) = f • C η)
  (hfix : ∀ i, C (w i) = w i)
  (hFp : ∀ c : Fin n → ℕ, ∑ i, c i • w i = 0 → ∀ i, p ∣ c i) :
-- imply
  LinearIndependent K w := by
-- proof
  classical
  have : ExpChar K p := .prime Fact.out
  have : PerfectRing K p := inferInstance
  have hsurj : ∀ y : K, ∃ x : K, x ^ p = y := by
    intro y
    obtain ⟨x, hx⟩ := (PerfectRing.bijective_frobenius (R := K) (p := p)).2 y
    exact ⟨x, hx⟩
  have hinj : ∀ x y : K, x ^ p = y ^ p → x = y := by
    intro x y hxy
    exact (PerfectRing.bijective_frobenius (R := K) (p := p)).1 hxy
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.strongInductionOn with
  | _ s IH =>
    intro g hsum
    if hall : ∀ i ∈ s, g i ≠ 0 then
      obtain rfl | ⟨i₀, hi₀⟩ := Finset.eq_empty_or_nonempty s
      ·
        intro i hi
        exact absurd hi (Finset.notMem_empty i)
      ·
        exfalso
        set h : Fin n → K := fun i => (g i₀)⁻¹ * g i with hh
        have hsum' : ∑ i ∈ s, h i • w i = 0 := by
          have e : ∀ i ∈ s, h i • w i = (g i₀)⁻¹ • (g i • w i) := by
            intro i _
            simp only [hh]
            exact mul_smul _ _ _
          rw [Finset.sum_congr rfl e, ← Finset.smul_sum, hsum, smul_zero]
        have hone : h i₀ = 1 := by
          simp only [hh]
          exact inv_mul_cancel₀ (hall i₀ hi₀)
        choose b hb using fun i => hsurj (h i)
        have hb₀ : b i₀ = 1 := by
          apply hinj
          rw [hb i₀, one_pow, hone]
        have hCterm : ∀ i ∈ s, C (h i • w i) = b i • w i := by
          intro i _
          have e1 : h i • w i = algebraMap K F (b i ^ p) • w i := by
            rw [algebraMap_smul, hb i]
          rw [e1, map_pow, hsemi, hfix, algebraMap_smul]
        have hrel2 : ∑ i ∈ s, b i • w i = 0 := by
          have e : ∑ i ∈ s, b i • w i = C (∑ i ∈ s, h i • w i) := by
            rw [map_sum]
            exact (Finset.sum_congr rfl hCterm).symm
          rw [e, hsum', map_zero]
        have hdiff : ∑ i ∈ s, (h i - b i) • w i = 0 := by
          have e : ∀ i ∈ s, (h i - b i) • w i = h i • w i - b i • w i := by
            intro i _
            exact sub_smul _ _ _
          rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, hsum', hrel2, sub_zero]
        have hi₀' : i₀ ∉ s.filter (fun i => h i - b i ≠ 0) := by
          intro hmem
          exact (Finset.mem_filter.mp hmem).2 (by rw [hone, hb₀, sub_self])
        have hss : s.filter (fun i => h i - b i ≠ 0) ⊂ s :=
          (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr ⟨i₀, hi₀, hi₀'⟩
        have hsum'' : ∑ i ∈ s.filter (fun i => h i - b i ≠ 0), (h i - b i) • w i = 0 := calc
            _ = ∑ i ∈ s, (h i - b i) • w i := by
              apply Finset.sum_subset (Finset.filter_subset _ _)
              intro i hi hni
              have h0 : ¬h i - b i ≠ 0 := fun hne => hni (Finset.mem_filter.mpr ⟨hi, hne⟩)
              rw [not_not.mp h0, zero_smul]
            _ = 0 := hdiff
        have hzero := IH _ hss (fun i => h i - b i) hsum''
        have hhb : ∀ i ∈ s, h i = b i := by
          intro i hi
          by_contra hne
          have hmem : i ∈ s.filter (fun i => h i - b i ≠ 0) :=
            Finset.mem_filter.mpr ⟨hi, fun h0 => hne (sub_eq_zero.mp h0)⟩
          refine (Finset.mem_filter.mp hmem).2 (hzero i hmem)
        have hfpx : ∀ i ∈ s, h i ^ p = h i := by
          intro i hi
          calc
            _ = b i ^ p := by rw [hhb i hi]
            _ = h i := hb i
        have hm : ∀ i ∈ s, ∃ mm : ℕ, (mm : K) = h i := by
          intro i hi
          exact exists_natCast_eq_of_pow_char_eq p (hfpx i hi)
        choose! m hmk using hm
        have hrel3 : ∑ i, (if i ∈ s then m i else 0) • w i = 0 := by
          have e1 : ∑ i ∈ s, (if i ∈ s then m i else 0) • w i = ∑ i, (if i ∈ s then m i else 0) • w i := by
            apply Finset.sum_subset (Finset.subset_univ s)
            intro i _ hni
            rw [ite_eq_right hni, zero_smul]
          have e2 : ∑ i ∈ s, (if i ∈ s then m i else 0) • w i = ∑ i ∈ s, h i • w i := by
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [ite_eq_left hi, ← hmk i hi, Nat.cast_smul_eq_nsmul K]
          rw [← e1, e2, hsum']
        have hdvd := hFp _ hrel3 i₀
        rw [ite_eq_left hi₀] at hdvd
        have hcontra : ((m i₀ : ℕ) : K) = 0 := (CharP.cast_eq_zero_iff K p _).mpr hdvd
        rw [hmk i₀ hi₀, hone] at hcontra
        exact one_ne_zero hcontra
    else
      push Not at hall
      obtain ⟨j, hj, hgj⟩ := hall
      have hss : s.filter (fun i => g i ≠ 0) ⊂ s :=
        (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr
          ⟨j, hj, fun hmem => (Finset.mem_filter.mp hmem).2 hgj⟩
      have hsum' : ∑ i ∈ s.filter (fun i => g i ≠ 0), g i • w i = 0 := calc
          _ = ∑ i ∈ s, g i • w i := by
            apply Finset.sum_subset (Finset.filter_subset _ _)
            intro i hi hni
            have h0 : ¬g i ≠ 0 := fun hne => hni (Finset.mem_filter.mpr ⟨hi, hne⟩)
            rw [not_not.mp h0, zero_smul]
          _ = 0 := hsum
      intro i hi
      if hgi : g i = 0 then
        exact hgi
      else
        exact IH _ hss g hsum' i (Finset.mem_filter.mpr ⟨hi, hgi⟩)


-- created on 2026-10-23
-- updated on 2026-10-24
