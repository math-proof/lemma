import Mathlib
import sympy.Basic
open Polynomial
open ValuationSubring


private lemma valuation_coeff_succ_lt_of_forall_not_mem
  {K : Type*}
  [Field K]
  (A : ValuationSubring K)
  (lc : K) (hlc : lc ≠ 0) (s : Multiset K)
  (hs : ∀ r ∈ s, r ∉ A) :
  (C lc * (s.map fun r => X - C r).prod).coeff 0 ≠ 0 ∧
  ∀ j : ℕ, A.valuation ((C lc * (s.map fun r => X - C r).prod).coeff (j + 1))
    < A.valuation ((C lc * (s.map fun r => X - C r).prod).coeff 0) := by
  induction s using Multiset.induction_on with
  | empty =>
    refine ⟨by simpa using hlc, fun j => ?_⟩
    simp only [Multiset.map_zero, Multiset.prod_zero, mul_one, coeff_C_succ, map_zero, coeff_C_zero]
    exact (Valuation.pos_iff _).mpr hlc
  | cons r s ih =>
    have hr : r ∉ A := hs r (Multiset.mem_cons_self r s)
    obtain ⟨h0, hj⟩ := ih fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    set p := C lc * (s.map fun r => X - C r).prod with hp
    clear_value p
    have hprod : C lc * ((r ::ₘ s).map fun r => X - C r).prod = (X - C r) * p := by
      rw [Multiset.map_cons, Multiset.prod_cons, hp]
      ring
    rw [hprod]
    have hr1 : 1 < A.valuation r := by
      rw [← not_le, valuation_le_one_iff]
      apply hr
    have hr0 : A.valuation r ≠ 0 := ne_of_gt (lt_trans zero_lt_one hr1)
    have hc0 : ((X - C r) * p).coeff 0 = -r * p.coeff 0 := by
      rw [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub]
    have hcs : ∀ j, ((X - C r) * p).coeff (j + 1) = p.coeff j - r * p.coeff (j + 1) := by
      intro j
      rw [sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul]
    have hv0 : A.valuation (((X - C r) * p).coeff 0) = A.valuation r * A.valuation (p.coeff 0) := by
      rw [hc0, map_mul, Valuation.map_neg]
    have hp0 : 0 < A.valuation (p.coeff 0) := (Valuation.pos_iff _).mpr h0
    refine ⟨?_, fun j => ?_⟩
    ·
      rw [hc0]
      exact mul_ne_zero (neg_ne_zero.mpr fun h => hr (h ▸ A.zero_mem)) h0
    ·
      rw [hv0, hcs]
      refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
      ·
        have hle : A.valuation (p.coeff j) ≤ A.valuation (p.coeff 0) := by
          cases j with
          | zero => exact le_rfl
          | succ j => exact le_of_lt (hj j)
        calc
          _ ≤ A.valuation (p.coeff 0) := hle
          _ = 1 * A.valuation (p.coeff 0) := (one_mul _).symm
          _ < A.valuation r * A.valuation (p.coeff 0) := mul_lt_mul_of_pos_right hr1 hp0
      ·
        rw [map_mul]
        exact mul_lt_mul_of_pos_left (hj j) (lt_trans zero_lt_one hr1)

private lemma map_residue_eq_C_of_forall_not_mem
  {K : Type*}
  [Field K]
  (A : ValuationSubring K)
  (g : Polynomial A)
  (hroots : ((g.map (algebraMap A K)).roots).card = (g.map (algebraMap A K)).natDegree)
  (hN : ∀ r ∈ (g.map (algebraMap A K)).roots, r ∉ A) :
  g.map (IsLocalRing.residue A) = C (IsLocalRing.residue A (g.coeff 0)) := by
  obtain rfl | hg0 := eq_or_ne g 0
  · simp
  set gK := g.map (algebraMap A K) with hgK
  have hgK0 : gK ≠ 0 := (Polynomial.map_ne_zero_iff (IsFractionRing.injective A K)).mpr hg0
  have hlc : gK.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hgK0
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
  obtain ⟨-, hlt⟩ := valuation_coeff_succ_lt_of_forall_not_mem A gK.leadingCoeff hlc gK.roots hN
  rw [hfac] at hlt
  ext n
  cases n with
  | zero => simp [coeff_map]
  | succ j =>
    rw [coeff_map, coeff_C_succ, IsLocalRing.residue_eq_zero_iff, valuation_lt_one_iff]
    have h1 : A.valuation (gK.coeff 0) ≤ 1 := by
      rw [hgK, coeff_map, valuation_le_one_iff]
      exact (g.coeff 0).2
    have h2 := hlt j
    simp only [hgK, coeff_map] at h2 h1
    exact lt_of_lt_of_le h2 h1

private lemma isRoot_of_isRoot_map
  {K : Type*}
  [Field K]
  (A : ValuationSubring K)
  {g : Polynomial A} {a : A} (h : (g.map (algebraMap A K)).IsRoot (a : K)) :
  g.IsRoot a := by
  rw [IsRoot, eval_map] at h
  change eval₂ (algebraMap A K) (algebraMap A K a) g = 0 at h
  rw [eval₂_hom] at h
  exact (IsFractionRing.injective A K) (by simpa using h)

open Classical in

private lemma rootMultiplicity_map_residue_eq_card_filter_roots_of_card_roots_eq
  {K : Type*}
  [Field K]
  (A : ValuationSubring K)
  (g : Polynomial A)
  (hg : g.map (IsLocalRing.residue A) ≠ 0)
  (hroots : ((g.map (algebraMap A K)).roots).card = (g.map (algebraMap A K)).natDegree)
  (b : IsLocalRing.ResidueField A) :
  (g.map (IsLocalRing.residue A)).rootMultiplicity b =
    ((g.map (algebraMap A K)).roots.filter fun r => ∃ h : r ∈ A, IsLocalRing.residue A ⟨r, h⟩ = b).card := by
  suffices H : ∀ (n : ℕ) (g : Polynomial A), g.natDegree = n → g.map (IsLocalRing.residue A) ≠ 0 →
      ((g.map (algebraMap A K)).roots).card = (g.map (algebraMap A K)).natDegree →
      (g.map (IsLocalRing.residue A)).rootMultiplicity b =
        ((g.map (algebraMap A K)).roots.filter fun r => ∃ h : r ∈ A, IsLocalRing.residue A ⟨r, h⟩ = b).card from
    H _ g rfl hg hroots
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g hn hg hroots
    have hg0 : g ≠ 0 := by
      rintro rfl
      exact hg (Polynomial.map_zero _)
    have hinj : Function.Injective (algebraMap A K) := (IsFractionRing.injective A K)
    have hgK0 : g.map (algebraMap A K) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hg0
    if hex : ∃ a : A, (g.map (algebraMap A K)).IsRoot (a : K) then
      obtain ⟨a, ha⟩ := hex
      have hga : g.IsRoot a := isRoot_of_isRoot_map A ha
      set h := g /ₘ (X - C a) with hh
      have hgh : g = (X - C a) * h := (mul_divByMonic_eq_iff_isRoot.mpr hga).symm
      have hh0 : h ≠ 0 := by
        rintro h0
        rw [h0, mul_zero] at hgh
        exact hg0 hgh
      have hdeg : g.natDegree = h.natDegree + 1 := by
        rw [hgh, natDegree_mul (X_sub_C_ne_zero a) hh0, natDegree_X_sub_C, add_comm]
      have hmapg : g.map (IsLocalRing.residue A) = (X - C (IsLocalRing.residue A a)) * h.map (IsLocalRing.residue A) := by
        rw [hgh, Polynomial.map_mul, Polynomial.map_sub, map_X, map_C]
      have hmapK : g.map (algebraMap A K) = (X - C (a : K)) * h.map (algebraMap A K) := by
        rw [hgh, Polynomial.map_mul, Polynomial.map_sub, map_X, map_C]
        rfl
      have hhred : h.map (IsLocalRing.residue A) ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hmapg
        exact hg hmapg
      have hhK0 : h.map (algebraMap A K) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hh0
      have hrootsK : (g.map (algebraMap A K)).roots = (a : K) ::ₘ (h.map (algebraMap A K)).roots := by
        rw [hmapK, roots_mul, roots_X_sub_C, Multiset.singleton_add]
        rw [← hmapK]
        apply hgK0
      have hdegK : (g.map (algebraMap A K)).natDegree = (h.map (algebraMap A K)).natDegree + 1 := by
        rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj, hdeg]
      have hrootsh : ((h.map (algebraMap A K)).roots).card = (h.map (algebraMap A K)).natDegree := by
        rw [hrootsK, Multiset.card_cons, hdegK] at hroots
        omega
      have IH := ih h.natDegree (by omega) h rfl hhred hrootsh
      rw [hmapg, rootMultiplicity_mul (hmapg ▸ hg), rootMultiplicity_X_sub_C, IH, hrootsK,
        Multiset.filter_cons, Multiset.card_add]
      have hpred : (∃ hmem : (a : K) ∈ A, IsLocalRing.residue A ⟨(a : K), hmem⟩ = b) ↔ b = IsLocalRing.residue A a := by
        constructor
        ·
          rintro ⟨hmem, hb⟩
          rw [← hb]
        ·
          intro hb
          exact ⟨a.2, hb.symm⟩
      if hb : b = IsLocalRing.residue A a then
        rw [ite_eq_left hb, ite_eq_left (hpred.mpr hb), Multiset.card_singleton]
      else
        rw [ite_eq_right hb, ite_eq_right (mt hpred.mp hb), Multiset.card_zero]
    else
      have hN : ∀ r ∈ (g.map (algebraMap A K)).roots, r ∉ A := by
        intro r hr hrA
        apply hex
        refine ⟨⟨r, hrA⟩, ?_⟩
        exact (mem_roots hgK0).mp hr
      have hC := map_residue_eq_C_of_forall_not_mem A g hroots hN
      rw [hC, rootMultiplicity_C]
      symm
      rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
      rintro r hr ⟨hrA, -⟩
      exact hN r hr hrA
open Classical in

private lemma rootMultiplicity_map_residue_eq_card_filter_roots
  {K : Type*}
  [Field K]
  (A : ValuationSubring K)
  (g : Polynomial A)
  (hg : g.map (IsLocalRing.residue A) ≠ 0) (hsplit : (g.map (algebraMap A K)).Splits)
  (b : IsLocalRing.ResidueField A) :
  (g.map (IsLocalRing.residue A)).rootMultiplicity b =
    ((g.map (algebraMap A K)).roots.filter fun r => ∃ h : r ∈ A, IsLocalRing.residue A ⟨r, h⟩ = b).card :=
  rootMultiplicity_map_residue_eq_card_filter_roots_of_card_roots_eq A g hg (splits_iff_card_roots.mp hsplit) b

private lemma isRoot_map_residue_of_mem
  {K : Type*}
  [Field K]
  (A : ValuationSubring K)
  {g : Polynomial A} {r : K} (hr : r ∈ A)
  (hroot : (g.map (algebraMap A K)).IsRoot r) :
  (g.map (IsLocalRing.residue A)).IsRoot (IsLocalRing.residue A ⟨r, hr⟩) := by
  have h := isRoot_of_isRoot_map A (a := ⟨r, hr⟩) hroot
  rw [IsRoot, eval_map, eval₂_hom, h.eq_zero, map_zero]

open Classical in

private lemma existsUnique_isRoot_residue_eq_of_rootMultiplicity_map_residue_eq_one'
  {K : Type*}
  [Field K]
  (A : ValuationSubring K)
  (g : Polynomial A)
  (hsplit : (g.map (algebraMap A K)).Splits)
  (b : IsLocalRing.ResidueField A) (hb : (g.map (IsLocalRing.residue A)).rootMultiplicity b = 1) :
  ∃! r : K, (g.map (algebraMap A K)).IsRoot r ∧ ∃ h : r ∈ A, IsLocalRing.residue A ⟨r, h⟩ = b := by
  have hg : g.map (IsLocalRing.residue A) ≠ 0 := by
    intro h0
    rw [h0, rootMultiplicity_zero] at hb
    exact zero_ne_one hb
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hg (Polynomial.map_zero _)
  have hgK0 : g.map (algebraMap A K) ≠ 0 := (Polynomial.map_ne_zero_iff (IsFractionRing.injective A K)).mpr hg0
  rw [rootMultiplicity_map_residue_eq_card_filter_roots A g hg hsplit b, Multiset.card_eq_one] at hb
  obtain ⟨r, hr⟩ := hb
  have hmem : r ∈ (g.map (algebraMap A K)).roots.filter
    fun r => ∃ h : r ∈ A, IsLocalRing.residue A ⟨r, h⟩ = b := by
    rw [hr]
    exact Multiset.mem_singleton_self r
  obtain ⟨hrr, hrb⟩ := Multiset.mem_filter.mp hmem
  refine ⟨r, ⟨(mem_roots hgK0).mp hrr, hrb⟩, fun r' ⟨hr'root, hr'b⟩ => ?_⟩
  have hmem' : r' ∈ (g.map (algebraMap A K)).roots.filter
    fun r => ∃ h : r ∈ A, IsLocalRing.residue A ⟨r, h⟩ = b :=
    Multiset.mem_filter.mpr ⟨(mem_roots hgK0).mpr hr'root, hr'b⟩
  rw [hr] at hmem'
  exact Multiset.mem_singleton.mp hmem'
/--
[ValuationSubring_existsUnique_isRoot_residue_eq_of_rootMultiplicity_map_residue_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_existsUnique_isRoot_residue_eq_of_rootMultiplicity_map_residue_eq_one.lean)
-/
@[path]
private lemma main
  [Field K]
  {A : ValuationSubring K}
  {g : Polynomial A}
  {b : IsLocalRing.ResidueField A}
-- given
  (hsplit : (g.map (algebraMap A K)).Splits)
  (hb : (g.map (IsLocalRing.residue A)).rootMultiplicity b = 1) :
-- imply
  ∃! r : K, (g.map (algebraMap A K)).IsRoot r ∧ ∃ h : r ∈ A, IsLocalRing.residue A ⟨r, h⟩ = b :=
-- proof
  existsUnique_isRoot_residue_eq_of_rootMultiplicity_map_residue_eq_one' A g hsplit b hb


-- created on 2026-10-23
