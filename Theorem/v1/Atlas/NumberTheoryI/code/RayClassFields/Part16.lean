/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.IdealFactorization
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.FinitePlaceAbsValue
import Theorem.v1.Atlas.NumberTheoryI.code.IdealFactorization.Part3
import Theorem.v1.Atlas.NumberTheoryI.code.FinitePlaceAbsValue
import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part24


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

attribute [instance] instFintypeSignsTimesUnits

lemma finset_prod_ideal_le_factor {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → Ideal R) (j : ι) (hj : j ∈ S) :
    S.prod f ≤ f j := by
  induction S using Finset.cons_induction with
  | empty => simp at hj
  | cons i s hi ih =>
    rw [Finset.prod_cons]
    rcases Finset.mem_cons.mp hj with rfl | hjs
    · exact Ideal.mul_le_right
    · exact le_trans Ideal.mul_le_left (ih hjs)

lemma unit_mod_ideal_not_in_prime {R : Type*} [CommRing R]
    {I 𝔭 : Ideal R} (hI𝔭 : I ≤ 𝔭) (h𝔭 : 𝔭 ≠ ⊤) {b : R}
    (hb : IsUnit (Ideal.Quotient.mk I b)) : b ∉ 𝔭 := by
  intro hb_mem
  let f := Ideal.Quotient.lift I (Ideal.Quotient.mk 𝔭) (fun r hr =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (hI𝔭 hr))
  have hunit : IsUnit (f (Ideal.Quotient.mk I b)) := hb.map f
  simp only [f, Ideal.Quotient.lift_mk] at hunit
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hb_mem] at hunit
  haveI : Nontrivial (R ⧸ 𝔭) := Ideal.Quotient.nontrivial_iff.mpr h𝔭
  exact not_isUnit_zero hunit

theorem coprime_rep_unit_eq_one_iff (𝔪 : @Modulus K _ _)
    {a b : NumberField.RingOfIntegers K}
    (ha : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal a))
    (hb : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal b))
    (hab : algebraMap (NumberField.RingOfIntegers K) K a /
             algebraMap (NumberField.RingOfIntegers K) K b = ((α : Kˣ) : K)) :
    ha.unit * hb.unit⁻¹ = 1 ↔
      ∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 →
        v.valuation K (((α : Kˣ) : K) - 1) ≤
          ↑(Multiplicative.ofAdd (-(𝔪 (Place.finite v) : ℤ))) := by
  classical


  have step1 : ha.unit * hb.unit⁻¹ = 1 ↔ a - b ∈ 𝔪.finitePartIdeal := by
    rw [mul_inv_eq_one]
    constructor
    · intro h
      have h' : (ha.unit : 𝓞 K ⧸ 𝔪.finitePartIdeal) = (hb.unit : 𝓞 K ⧸ 𝔪.finitePartIdeal) :=
        congr_arg Units.val h
      simp only [IsUnit.unit_spec] at h'
      exact Ideal.Quotient.eq.mp h'
    · intro h
      ext; simp only [IsUnit.unit_spec]; exact Ideal.Quotient.eq.mpr h
  rw [step1]

  set S := (𝔪.finite_support.preimage (f := Place.finite)
    (fun a _ b _ hab => by cases hab; rfl)).toFinset with hS_def


  have hb_ne_zero : (algebraMap (NumberField.RingOfIntegers K) K) b ≠ 0 := by
    intro h0
    simp [h0] at hab
    exact (Units.ne_zero α) hab.symm


  have hα_sub : ((α : Kˣ) : K) - 1 =
      algebraMap (NumberField.RingOfIntegers K) K (a - b) /
        algebraMap (NumberField.RingOfIntegers K) K b := by
    rw [← hab, map_sub]; field_simp

  have hv_in_S : ∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 → v ∈ S := by
    intro v hv
    simp only [hS_def, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq]
    exact hv

  have hI_le : ∀ v ∈ S, 𝔪.finitePartIdeal ≤ v.asIdeal ^ 𝔪 (Place.finite v) := by
    intro v hv
    exact finset_prod_ideal_le_factor S _ v hv

  have hb_not_mem : ∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 → b ∉ v.asIdeal := by
    intro v hv
    exact unit_mod_ideal_not_in_prime
      (le_trans (hI_le v (hv_in_S v hv)) (Ideal.pow_le_self hv))
      v.isPrime.ne_top hb


  have hvb_one : ∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 →
      v.intValuation b = 1 := by
    intro v hv
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr (hb_not_mem v hv)

  have hval_eq : ∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 →
      v.valuation K (((α : Kˣ) : K) - 1) = v.intValuation (a - b) := by
    intro v hv
    rw [hα_sub, Valuation.map_div,
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        hvb_one v hv, div_one]

  have hval_mem : ∀ v : FinitePlace K, ∀ n : ℕ,
      v.intValuation (a - b) ≤ ↑(Multiplicative.ofAdd (-(n : ℤ))) ↔
        a - b ∈ v.asIdeal ^ n := by
    intro v n
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v (a - b) n

  constructor
  ·
    intro hmem v hv
    rw [hval_eq v hv, hval_mem v]
    exact hI_le v (hv_in_S v hv) hmem
  ·
    intro hval

    have hcrt : S.inf (fun 𝔭 => 𝔭.asIdeal ^ 𝔪 (Place.finite 𝔭)) =
        S.prod (fun 𝔭 => 𝔭.asIdeal ^ 𝔪 (Place.finite 𝔭)) :=
      IsDedekindDomain.HeightOneSpectrum.inf_pow_eq_prod S
        (fun 𝔭 => 𝔪 (Place.finite 𝔭)) id (fun _ hi _ hj hij => hij)

    rw [show 𝔪.finitePartIdeal = S.prod (fun 𝔭 => 𝔭.asIdeal ^ 𝔪 (Place.finite 𝔭)) from rfl,
        ← hcrt, Submodule.mem_finsetInf]
    intro v hv
    have hv_ne : 𝔪 (Place.finite v) ≠ 0 := by
      simp only [hS_def, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq] at hv
      exact hv
    rw [← hval_mem v, ← hval_eq v hv_ne]
    exact hval v hv_ne

theorem finitePartMapHom_ker_iff (𝔪 : @Modulus K _ _)
    (α : UnitsCoprime_subgroup' K 𝔪) :
    finitePartMapHom K 𝔪 α = 1 ↔
      ∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 →
        v.valuation K (((α : Kˣ) : K) - 1) ≤
          ↑(Multiplicative.ofAdd (-(𝔪 (Place.finite v) : ℤ))) := by

  show finitePartMapFn K 𝔪 α = 1 ↔ _
  simp only [finitePartMapFn]

  have h := coprime_rep_exists 𝔪 α
  have ha := h.choose_spec.choose_spec.1
  have hb := h.choose_spec.choose_spec.2.1
  have heq := h.choose_spec.choose_spec.2.2

  exact coprime_rep_unit_eq_one_iff (α := (α : Kˣ)) 𝔪 ha hb heq

theorem weak_approx_nonzero_with_val_and_sign {K : Type*} [Field K] [NumberField K]
    (𝔪 : @Modulus K _ _)
    (pos : 𝔪.infSupportFinset → Prop) [DecidablePred pos] :
    ∃ (x : K) (_ : x ≠ 0),
      (∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 → v.valuation K x = 1) ∧
      (∀ (w : NumberField.InfinitePlace K) (hw : w ∈ 𝔪.infSupportFinset),
        (pos ⟨w, hw⟩ → 0 < (w.embedding x).re) ∧
        (¬ pos ⟨w, hw⟩ → (w.embedding x).re < 0)) := by
  classical

  let S_fin : Finset (FinitePlace K) :=
    (𝔪.finite_support.preimage (f := Place.finite)
      (fun a _ b _ hab => by cases hab; rfl)).toFinset
  let S_inf := 𝔪.infSupportFinset

  let w₀ : NumberField.InfinitePlace K := Classical.arbitrary _
  let S_inf' : Finset (NumberField.InfinitePlace K) := S_inf ∪ {w₀}

  let ι := (↥S_fin) ⊕ (↥S_inf')

  let absVals : ι → AbsoluteValue K ℝ := fun i => match i with
    | .inl ⟨v, _⟩ => FinitePlace.toAbsoluteValue v
    | .inr ⟨w, _⟩ => w.val

  have hNontrivial : ∀ i, (absVals i).IsNontrivial := fun i => match i with
    | .inl ⟨v, _⟩ => FinitePlace.toAbsoluteValue_isNontrivial v
    | .inr ⟨w, _⟩ => by
        show w.val.IsNontrivial
        refine ⟨2, two_ne_zero, ?_⟩
        rw [show w.val 2 = w 2 from rfl,
            ← NumberField.InfinitePlace.norm_embedding_eq, map_ofNat]
        simp

  have hIneq : ∀ i j, i ≠ j → ¬ (absVals i).IsEquiv (absVals j) := by
    intro i j hij
    match i, j with
    | .inl ⟨v₁, _⟩, .inl ⟨v₂, _⟩ =>
      have hne : v₁ ≠ v₂ := fun h => hij (by subst h; rfl)
      exact FinitePlace.toAbsoluteValue_pairwise_inequiv v₁ v₂ hne
    | .inr ⟨w₁, _⟩, .inr ⟨w₂, _⟩ =>
      have hne : w₁ ≠ w₂ := fun h => hij (by subst h; rfl)
      intro heq
      exact hne (NumberField.InfinitePlace.eq_iff_isEquiv.mpr (show w₁.val.IsEquiv w₂.val from heq))
    | .inl ⟨v, _⟩, .inr ⟨w, _⟩ =>
      intro heq

      have hna_v : IsNonarchimedean (FinitePlace.toAbsoluteValue v) := by
        intro a b
        exact NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v a b

      have hna_w : IsNonarchimedean (w.val) := by
        intro a b
        have h1 := hna_v a b
        change FinitePlace.toAbsoluteValue v (a + b) ≤
          FinitePlace.toAbsoluteValue v a ⊔ FinitePlace.toAbsoluteValue v b at h1
        rcases le_total (FinitePlace.toAbsoluteValue v a) (FinitePlace.toAbsoluteValue v b) with hab | hab
        · exact le_trans ((heq (a + b) b).mp (le_trans h1 (sup_le hab le_rfl))) le_sup_right
        · exact le_trans ((heq (a + b) a).mp (le_trans h1 (sup_le le_rfl hab))) le_sup_left

      have h2 : w.val 2 = 2 := by
        rw [show w.val 2 = w 2 from rfl,
            ← NumberField.InfinitePlace.norm_embedding_eq, map_ofNat, Complex.norm_ofNat]
      have hle := hna_w 1 1
      simp only [show (1 : K) + 1 = 2 from by ring] at hle
      rw [h2, map_one] at hle; simp only [max_self] at hle; linarith
    | .inr ⟨w, _⟩, .inl ⟨v, _⟩ =>
      intro heq
      have hna_v : IsNonarchimedean (FinitePlace.toAbsoluteValue v) := by
        intro a b
        exact NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v a b
      have heq' := AbsoluteValue.IsEquiv.symm heq
      have hna_w : IsNonarchimedean (w.val) := by
        intro a b
        have h1 := hna_v a b
        change FinitePlace.toAbsoluteValue v (a + b) ≤
          FinitePlace.toAbsoluteValue v a ⊔ FinitePlace.toAbsoluteValue v b at h1
        rcases le_total (FinitePlace.toAbsoluteValue v a) (FinitePlace.toAbsoluteValue v b) with hab | hab
        · exact le_trans ((heq' (a + b) b).mp (le_trans h1 (sup_le hab le_rfl))) le_sup_right
        · exact le_trans ((heq' (a + b) a).mp (le_trans h1 (sup_le le_rfl hab))) le_sup_left
      have h2 : w.val 2 = 2 := by
        rw [show w.val 2 = w 2 from rfl,
            ← NumberField.InfinitePlace.norm_embedding_eq, map_ofNat, Complex.norm_ofNat]
      have hle := hna_w 1 1
      simp only [show (1 : K) + 1 = 2 from by ring] at hle
      rw [h2, map_one] at hle; simp only [max_self] at hle; linarith

  let target : ι → K := fun i => match i with
    | .inl _ => 1
    | .inr ⟨w, hw⟩ =>
      if h : w ∈ S_inf then
        if pos ⟨w, h⟩ then 1 else -1
      else 1
  let ε : ι → ℝ := fun _ => 1 / 2

  obtain ⟨x, hx⟩ := weak_approximation_theorem absVals hNontrivial hIneq target ε
    (fun _ => by norm_num)

  refine ⟨x, ?_, ?_, ?_⟩
  ·
    intro hx0
    have hmem : w₀ ∈ S_inf' := Finset.mem_union_right _ (Finset.mem_singleton_self _)
    have hi := hx (.inr ⟨w₀, hmem⟩)
    simp only [target, absVals] at hi
    rw [hx0] at hi

    split_ifs at hi with h1 h2
    all_goals (
      simp only [ε, show (0 : K) - 1 = -1 from by ring,
        show (0 : K) - -1 = 1 from by ring,
        AbsoluteValue.map_neg, map_one] at hi; linarith)

  ·
    intro v hv
    have hvmem : v ∈ S_fin := by
      simp only [S_fin, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq]
      exact hv
    have hi := hx (.inl ⟨v, hvmem⟩)
    simp only [target, absVals, FinitePlace.toAbsoluteValue] at hi

    have hi' : NumberField.HeightOneSpectrum.adicAbv K v (x - 1) < 1 / 2 := by
      simp only [ε] at hi; exact hi
    have hlt1 : NumberField.HeightOneSpectrum.adicAbv K v (x - 1) < 1 := by linarith
    have hna := NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v
    have h1_val : NumberField.HeightOneSpectrum.adicAbv K v 1 = 1 := map_one _
    have hlt_strict : NumberField.HeightOneSpectrum.adicAbv K v (x - 1) <
        NumberField.HeightOneSpectrum.adicAbv K v 1 := by rw [h1_val]; exact hlt1
    have hmax := IsNonarchimedean.add_eq_max_of_ne hna hlt_strict.ne
    rw [sub_add_cancel] at hmax
    have hxeq1 : NumberField.HeightOneSpectrum.adicAbv K v x = 1 := by
      rw [hmax, h1_val, max_eq_right (le_of_lt hlt1)]

    have hne0 := NumberField.HeightOneSpectrum.absNorm_ne_zero (R := 𝓞 K) v
    have hne1 := ne_of_gt (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal (R := 𝓞 K) v)
    rw [NumberField.HeightOneSpectrum.adicAbv_def] at hxeq1
    have hnnr : WithZeroMulInt.toNNReal hne0 (v.valuation K x) = 1 := by exact_mod_cast hxeq1
    exact (WithZeroMulInt.toNNReal_eq_one_iff _ hne0 hne1).mp hnnr
  ·
    intro w hw
    have hwmem : w ∈ S_inf' := Finset.mem_union_left _ hw
    have hi := hx (.inr ⟨w, hwmem⟩)
    simp only [target, absVals, show w ∈ S_inf from hw, dite_true] at hi

    have hw_real := 𝔪.infSupportFinset_isReal hw

    have him_eq : ∀ y : K, (w.embedding y).im = 0 := by
      intro y
      have hr := NumberField.InfinitePlace.isReal_iff.mp hw_real
      have hconj : starRingEnd ℂ (w.embedding y) = w.embedding y :=
        RingHom.congr_fun hr y
      rwa [Complex.conj_eq_iff_im] at hconj

    have hw_val_eq : ∀ y : K, w.val y = ‖w.embedding y‖ := by
      intro y; exact (NumberField.InfinitePlace.norm_embedding_eq w y).symm

    have norm_eq_abs_re : ∀ y : K, ‖w.embedding y‖ = |((w.embedding y).re)| := by
      intro y
      have hze : (w.embedding y) = ↑(w.embedding y).re :=
        Complex.ext rfl (by simp [him_eq y])
      rw [hze, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
    constructor
    ·
      intro hpos
      simp only [hpos, ite_true] at hi

      have habs : |((w.embedding (x - 1)).re)| < 1 / 2 := by
        have : w.val (x - 1) = ‖w.embedding (x - 1)‖ := hw_val_eq (x - 1)
        rw [this, norm_eq_abs_re (x - 1)] at hi
        exact hi
      rw [map_sub, Complex.sub_re, map_one, Complex.one_re, abs_lt] at habs
      linarith [habs.1]
    ·
      intro hnpos
      simp only [hnpos, ite_false] at hi
      have habs : |((w.embedding (x - (-1))).re)| < 1 / 2 := by
        have : w.val (x - (-1)) = ‖w.embedding (x - (-1))‖ := hw_val_eq (x - (-1))
        rw [this, norm_eq_abs_re (x - (-1))] at hi
        exact hi
      rw [map_sub, map_neg, map_one, Complex.sub_re, Complex.neg_re, Complex.one_re] at habs
      rw [show (w.embedding x).re - -1 = (w.embedding x).re + 1 from by ring, abs_lt] at habs
      linarith [habs.2]

theorem weak_approx_sign_coprime {K : Type*} [Field K] [NumberField K]
    (𝔪 : @Modulus K _ _)
    (s : 𝔪.infSupportFinset → Multiplicative (ZMod 2)) :
    ∃ (α : Kˣ),
      (∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 → v.valuation K (α : K) = 1) ∧
      (∀ (w : NumberField.InfinitePlace K) (hw : w ∈ 𝔪.infSupportFinset),
        Multiplicative.ofAdd (signAtPlace (𝔪.infSupportFinset_isReal hw) α) = s ⟨w, hw⟩) := by
  classical

  let pos : 𝔪.infSupportFinset → Prop := fun wh => s wh = 1
  obtain ⟨x, hx_ne, hval, hsign⟩ := weak_approx_nonzero_with_val_and_sign 𝔪 pos

  refine ⟨Units.mk0 x hx_ne, hval, ?_⟩
  intro w hw
  simp only [signAtPlace, Units.val_mk0]
  have ⟨hpos_case, hneg_case⟩ := hsign w hw


  by_cases hp : pos ⟨w, hw⟩
  ·
    have hre_pos := hpos_case hp
    simp [hre_pos]
    change Multiplicative.ofAdd (0 : ZMod 2) = s ⟨w, hw⟩
    exact hp.symm
  ·
    have hre_neg := hneg_case hp
    simp only [show ¬(0 < (w.embedding x).re) from not_lt.mpr (le_of_lt hre_neg), ite_false]
    change Multiplicative.ofAdd (1 : ZMod 2) = s ⟨w, hw⟩


    have : ∀ (a : Multiplicative (ZMod 2)),
        a = Multiplicative.ofAdd 0 ∨ a = Multiplicative.ofAdd 1 := by
      intro a
      rcases Multiplicative.ofAdd.surjective a with ⟨b, rfl⟩
      fin_cases b <;> first | left; rfl | right; rfl
    rcases this (s ⟨w, hw⟩) with h | h
    · exfalso; exact hp h
    · exact h.symm

theorem signMapHom_surjective (𝔪 : @Modulus K _ _) :
    Function.Surjective (signMapHom K 𝔪) := by
  intro s
  exact signMapHom_surjective_aux 𝔪 s
where
  signMapHom_surjective_aux : ∀ (𝔪 : @Modulus K _ _)
      (s : 𝔪.infSupportFinset → Multiplicative (ZMod 2)),
      ∃ α : UnitsCoprime_subgroup' K 𝔪, signMapHom K 𝔪 α = s := by
    intro 𝔪 s


    obtain ⟨α, hcoprime, hsigns⟩ := weak_approx_sign_coprime 𝔪 s

    have hmem : (α : Kˣ) ∈ UnitsCoprime_subgroup' K 𝔪 := by
      intro v hv
      exact hcoprime v hv
    refine ⟨⟨α, hmem⟩, ?_⟩

    funext ⟨w, hw⟩
    simp only [signMapHom]
    exact hsigns w hw

theorem weak_approx_coprime_sign_finitePart {K : Type*} [Field K] [NumberField K]
    (𝔪 : @Modulus K _ _)
    (u : (NumberField.RingOfIntegers K ⧸ 𝔪.finitePartIdeal)ˣ) :
    ∃ (α : UnitsCoprime_subgroup' K 𝔪),
      signMapHom K 𝔪 α = 1 ∧ finitePartMapHom K 𝔪 α = u := by
  classical

  by_cases htriv : Subsingleton (NumberField.RingOfIntegers K ⧸ 𝔪.finitePartIdeal)
  · haveI := htriv
    exact ⟨1, by simp [MonoidHom.map_one], by simp [MonoidHom.map_one, Subsingleton.eq_one u]⟩
  · rw [not_subsingleton_iff_nontrivial] at htriv; haveI := htriv

    obtain ⟨r, hr_lift⟩ : ∃ r : 𝓞 K,
        Ideal.Quotient.mk 𝔪.finitePartIdeal r = (u : 𝓞 K ⧸ 𝔪.finitePartIdeal) :=
      Ideal.Quotient.mk_surjective (u : 𝓞 K ⧸ 𝔪.finitePartIdeal)
    have hr_unit : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal r) := by
      rw [hr_lift]; exact u.isUnit
    have hr_ne_zero : r ≠ 0 := by
      intro h; rw [h, map_zero] at hr_lift; exact not_isUnit_zero (hr_lift ▸ u.isUnit)
    have halg_ne : algebraMap (𝓞 K) K r ≠ 0 := by
      rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ K)]

    let α_r : Kˣ := Units.mk0 (algebraMap (𝓞 K) K r) halg_ne
    have hα_r_coprime : (α_r : Kˣ) ∈ UnitsCoprime_subgroup' K 𝔪 := by
      intro v hv
      have hr_not_in_v : r ∉ v.asIdeal := by
        apply unit_mod_ideal_not_in_prime _ v.isPrime.ne_top hr_unit
        set S := (𝔪.finite_support.preimage (f := Place.finite)
          (fun a _ b _ hab => by cases hab; rfl)).toFinset with hS_def
        have hvmem : v ∈ S := by
          simp only [hS_def, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq]
          exact hv
        exact le_trans (finset_prod_ideal_le_factor S _ v hvmem) (Ideal.pow_le_self hv)

      simp only [Units.val_mk0, α_r]
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr hr_not_in_v
    let α₀ : UnitsCoprime_subgroup' K 𝔪 := ⟨α_r, hα_r_coprime⟩


    have hfp_α₀ : finitePartMapHom K 𝔪 α₀ = u := by
      show finitePartMapFn K 𝔪 α₀ = u
      simp only [finitePartMapFn]
      have h := coprime_rep_exists 𝔪 α₀
      have ha_rep := h.choose_spec.choose_spec.1
      have hb_rep := h.choose_spec.choose_spec.2.1
      have heq_rep := h.choose_spec.choose_spec.2.2
      have h1_unit : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal (1 : 𝓞 K)) := isUnit_one
      have heq_our : algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K 1 = ((α₀ : Kˣ) : K) := by
        simp [Units.val_mk0, α_r, α₀]

      have hwd := coprime_rep_well_def 𝔪 ha_rep hb_rep hr_unit h1_unit
        (by rw [heq_our]; exact heq_rep)
      rw [hwd]
      have hu_eq : hr_unit.unit = u := by ext; simp [IsUnit.unit_spec, hr_lift]
      have h1_eq : h1_unit.unit = 1 := by ext; simp
      simp [hu_eq, h1_eq]


    let S_fin : Finset (FinitePlace K) :=
      (𝔪.finite_support.preimage (f := Place.finite)
        (fun a _ b _ hab => by cases hab; rfl)).toFinset
    let S_inf := 𝔪.infSupportFinset
    let w₀ : NumberField.InfinitePlace K := Classical.arbitrary _
    let S_inf' : Finset (NumberField.InfinitePlace K) := S_inf ∪ {w₀}
    let ι := (↥S_fin) ⊕ (↥S_inf')
    let absVals : ι → AbsoluteValue K ℝ := fun i => match i with
      | .inl ⟨v, _⟩ => FinitePlace.toAbsoluteValue v
      | .inr ⟨w, _⟩ => w.val
    have hNontrivial : ∀ i, (absVals i).IsNontrivial := fun i => match i with
      | .inl ⟨v, _⟩ => FinitePlace.toAbsoluteValue_isNontrivial v
      | .inr ⟨w, _⟩ => by
          show w.val.IsNontrivial
          refine ⟨2, two_ne_zero, ?_⟩
          rw [show w.val 2 = w 2 from rfl,
              ← NumberField.InfinitePlace.norm_embedding_eq, map_ofNat]
          simp
    have hIneq : ∀ i j, i ≠ j → ¬ (absVals i).IsEquiv (absVals j) := by
      intro i j hij
      match i, j with
      | .inl ⟨v₁, _⟩, .inl ⟨v₂, _⟩ =>
        have hne : v₁ ≠ v₂ := fun h => hij (by subst h; rfl)
        exact FinitePlace.toAbsoluteValue_pairwise_inequiv v₁ v₂ hne
      | .inr ⟨w₁, _⟩, .inr ⟨w₂, _⟩ =>
        have hne : w₁ ≠ w₂ := fun h => hij (by subst h; rfl)
        intro heq
        exact hne (NumberField.InfinitePlace.eq_iff_isEquiv.mpr
          (show w₁.val.IsEquiv w₂.val from heq))
      | .inl ⟨v, _⟩, .inr ⟨w, _⟩ =>
        intro heq
        have hna_v : IsNonarchimedean (FinitePlace.toAbsoluteValue v) := by
          intro a b; exact NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v a b
        have hna_w : IsNonarchimedean (w.val) := by
          intro a b
          have h1 := hna_v a b
          change FinitePlace.toAbsoluteValue v (a + b) ≤
            FinitePlace.toAbsoluteValue v a ⊔ FinitePlace.toAbsoluteValue v b at h1
          rcases le_total (FinitePlace.toAbsoluteValue v a)
            (FinitePlace.toAbsoluteValue v b) with hab | hab
          · exact le_trans ((heq (a + b) b).mp (le_trans h1 (sup_le hab le_rfl))) le_sup_right
          · exact le_trans ((heq (a + b) a).mp (le_trans h1 (sup_le le_rfl hab))) le_sup_left
        have h2 : w.val 2 = 2 := by
          rw [show w.val 2 = w 2 from rfl,
              ← NumberField.InfinitePlace.norm_embedding_eq, map_ofNat, Complex.norm_ofNat]
        have hle := hna_w 1 1
        simp only [show (1 : K) + 1 = 2 from by ring] at hle
        rw [h2, map_one] at hle; simp only [max_self] at hle; linarith
      | .inr ⟨w, _⟩, .inl ⟨v, _⟩ =>
        intro heq
        have hna_v : IsNonarchimedean (FinitePlace.toAbsoluteValue v) := by
          intro a b; exact NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v a b
        have heq' := AbsoluteValue.IsEquiv.symm heq
        have hna_w : IsNonarchimedean (w.val) := by
          intro a b
          have h1 := hna_v a b
          change FinitePlace.toAbsoluteValue v (a + b) ≤
            FinitePlace.toAbsoluteValue v a ⊔ FinitePlace.toAbsoluteValue v b at h1
          rcases le_total (FinitePlace.toAbsoluteValue v a)
            (FinitePlace.toAbsoluteValue v b) with hab | hab
          · exact le_trans ((heq' (a + b) b).mp (le_trans h1 (sup_le hab le_rfl))) le_sup_right
          · exact le_trans ((heq' (a + b) a).mp (le_trans h1 (sup_le le_rfl hab))) le_sup_left
        have h2 : w.val 2 = 2 := by
          rw [show w.val 2 = w 2 from rfl,
              ← NumberField.InfinitePlace.norm_embedding_eq, map_ofNat, Complex.norm_ofNat]
        have hle := hna_w 1 1
        simp only [show (1 : K) + 1 = 2 from by ring] at hle
        rw [h2, map_one] at hle; simp only [max_self] at hle; linarith

    let target : ι → K := fun i => match i with
      | .inl _ => algebraMap (𝓞 K) K r
      | .inr _ => 1


    let εfin (v : FinitePlace K) : ℝ :=
      min (1 / 2) ((Ideal.absNorm v.asIdeal : ℝ) ^
        (-(𝔪 (Place.finite v) - 1 : ℤ)))
    let ε : ι → ℝ := fun i => match i with
      | .inl ⟨v, _⟩ => εfin v
      | .inr _ => 1 / 2
    have hε_pos : ∀ i, 0 < ε i := by
      intro i; match i with
      | .inl ⟨v, _⟩ =>
        show 0 < min (1 / 2) _
        apply lt_min (by norm_num)
        apply zpow_pos
        have h := NumberField.HeightOneSpectrum.absNorm_ne_zero (R := 𝓞 K) v
        exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by exact_mod_cast h))
      | .inr _ => norm_num

    obtain ⟨x, hx⟩ := weak_approximation_theorem absVals hNontrivial hIneq target ε hε_pos

    have hx_ne : x ≠ 0 := by
      intro hx0
      have hmem : w₀ ∈ S_inf' := Finset.mem_union_right _ (Finset.mem_singleton_self _)
      have hi := hx (.inr ⟨w₀, hmem⟩)
      simp only [target, absVals, ε] at hi
      rw [hx0, show (0 : K) - 1 = -1 from by ring, AbsoluteValue.map_neg, map_one] at hi
      linarith

    have hx_coprime : ∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 →
        v.valuation K x = 1 := by
      intro v hv
      have hvmem : v ∈ S_fin := by
        simp only [S_fin, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq]; exact hv
      have hi := hx (.inl ⟨v, hvmem⟩)
      simp only [target, absVals, FinitePlace.toAbsoluteValue, ε, εfin] at hi

      have hlt_half : NumberField.HeightOneSpectrum.adicAbv K v (x - algebraMap (𝓞 K) K r) < 1 / 2 := by
        exact lt_of_lt_of_le hi (min_le_left _ _)

      have halg_r_val : v.valuation K (algebraMap (𝓞 K) K r) = 1 := by
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr
          (unit_mod_ideal_not_in_prime
            (le_trans (finset_prod_ideal_le_factor S_fin _ v hvmem) (Ideal.pow_le_self hv))
            v.isPrime.ne_top hr_unit)
      have halg_r_abv : NumberField.HeightOneSpectrum.adicAbv K v (algebraMap (𝓞 K) K r) = 1 := by
        rw [NumberField.HeightOneSpectrum.adicAbv_def]
        have hne0 := NumberField.HeightOneSpectrum.absNorm_ne_zero (R := 𝓞 K) v
        have hne1 := ne_of_gt (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal (R := 𝓞 K) v)
        have := (WithZeroMulInt.toNNReal_eq_one_iff _ hne0 hne1).mpr halg_r_val
        exact_mod_cast this
      have hlt1 : NumberField.HeightOneSpectrum.adicAbv K v (x - algebraMap (𝓞 K) K r) < 1 := by
        linarith
      have hlt_r : NumberField.HeightOneSpectrum.adicAbv K v (x - algebraMap (𝓞 K) K r) <
          NumberField.HeightOneSpectrum.adicAbv K v (algebraMap (𝓞 K) K r) := by
        rw [halg_r_abv]; exact hlt1
      have hna := NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v
      have hmax := IsNonarchimedean.add_eq_max_of_ne hna hlt_r.ne
      rw [sub_add_cancel] at hmax
      have hxeq : NumberField.HeightOneSpectrum.adicAbv K v x = 1 := by
        rw [hmax, halg_r_abv, max_eq_right (le_of_lt hlt1)]
      have hne0 := NumberField.HeightOneSpectrum.absNorm_ne_zero (R := 𝓞 K) v
      have hne1 := ne_of_gt (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal (R := 𝓞 K) v)
      rw [NumberField.HeightOneSpectrum.adicAbv_def] at hxeq
      have hnnr : WithZeroMulInt.toNNReal hne0 (v.valuation K x) = 1 := by exact_mod_cast hxeq
      exact (WithZeroMulInt.toNNReal_eq_one_iff _ hne0 hne1).mp hnnr

    let x_unit : Kˣ := Units.mk0 x hx_ne
    have hx_mem : (x_unit : Kˣ) ∈ UnitsCoprime_subgroup' K 𝔪 := by
      intro v hv; simp only [Units.val_mk0, x_unit]; exact hx_coprime v hv
    let α_x : UnitsCoprime_subgroup' K 𝔪 := ⟨x_unit, hx_mem⟩

    have hsign_x : signMapHom K 𝔪 α_x = 1 := by
      funext ⟨w, hw⟩
      simp only [Pi.one_apply, signMapHom, signAtPlace]
      have hwmem : w ∈ S_inf' := Finset.mem_union_left _ hw
      have hi := hx (.inr ⟨w, hwmem⟩)
      simp only [target, absVals, ε] at hi
      have hw_real := 𝔪.infSupportFinset_isReal hw
      have him := embedding_im_zero hw_real x
      have hw_val_eq : w.val (x - 1) = ‖w.embedding (x - 1)‖ :=
        (NumberField.InfinitePlace.norm_embedding_eq w (x - 1)).symm
      have norm_eq : ‖w.embedding (x - 1)‖ = |((w.embedding (x - 1)).re)| := by
        have hze : (w.embedding (x - 1)) = ↑(w.embedding (x - 1)).re :=
          Complex.ext rfl (by simp [embedding_im_zero hw_real])
        rw [hze, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
      rw [hw_val_eq, norm_eq] at hi
      rw [map_sub, Complex.sub_re, map_one, Complex.one_re, abs_lt] at hi
      have hpos : 0 < (w.embedding (x : K)).re := by linarith [hi.1]
      show Multiplicative.ofAdd (if 0 < (w.embedding x).re then (0 : ZMod 2) else 1) = 1
      rw [if_pos hpos]
      rfl


    have hfp_x : finitePartMapHom K 𝔪 α_x = u := by


      have hprod : α_x = α_x * α₀⁻¹ * α₀ := by group
      rw [hprod, map_mul, hfp_α₀]
      suffices finitePartMapHom K 𝔪 (α_x * α₀⁻¹) = 1 by rw [this, one_mul]
      rw [finitePartMapHom_ker_iff]
      intro v hv


      have hvmem : v ∈ S_fin := by
        simp only [S_fin, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq]; exact hv
      have hi := hx (.inl ⟨v, hvmem⟩)
      simp only [target, absVals, FinitePlace.toAbsoluteValue, ε, εfin] at hi

      have hval_quot : ((α_x * α₀⁻¹ : UnitsCoprime_subgroup' K 𝔪) : Kˣ) =
          x_unit * α_r⁻¹ := by
        simp [α_x, α₀, Subgroup.coe_mul, Subgroup.coe_inv]
      have hval_K : (((α_x * α₀⁻¹ : UnitsCoprime_subgroup' K 𝔪) : Kˣ) : K) =
          x * (algebraMap (𝓞 K) K r)⁻¹ := by
        rw [hval_quot]; simp [Units.val_mul, Units.val_inv_eq_inv_val, x_unit, α_r]
      rw [hval_K]

      have hsub_eq : x * (algebraMap (𝓞 K) K r)⁻¹ - 1 =
          (x - algebraMap (𝓞 K) K r) * (algebraMap (𝓞 K) K r)⁻¹ := by
        rw [sub_mul, mul_inv_cancel₀ halg_ne]
      rw [hsub_eq, Valuation.map_mul, Valuation.map_inv]

      have halg_r_val : v.valuation K (algebraMap (𝓞 K) K r) = 1 := by
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr
          (unit_mod_ideal_not_in_prime
            (le_trans (finset_prod_ideal_le_factor S_fin _ v hvmem) (Ideal.pow_le_self hv))
            v.isPrime.ne_top hr_unit)
      rw [halg_r_val, inv_one, mul_one]


      have hlt_thresh : NumberField.HeightOneSpectrum.adicAbv K v
          (x - algebraMap (𝓞 K) K r) <
          ((Ideal.absNorm v.asIdeal : ℝ) ^
            (-(𝔪 (Place.finite v) - 1 : ℤ))) := by
        exact lt_of_lt_of_le hi (min_le_right _ _)


      have hne0 := NumberField.HeightOneSpectrum.absNorm_ne_zero (R := 𝓞 K) v
      have hne1 := ne_of_gt (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal (R := 𝓞 K) v)

      rw [NumberField.HeightOneSpectrum.adicAbv_def] at hlt_thresh


      set n := 𝔪 (Place.finite v) with hn_def
      set val_y := v.valuation K (x - algebraMap (𝓞 K) K r) with hval_y_def

      have htoNNReal_coe : WithZeroMulInt.toNNReal hne0
          (↑(Multiplicative.ofAdd (-(↑n - 1 : ℤ))) : WithZero (Multiplicative ℤ)) =
          (↑(Ideal.absNorm v.asIdeal) : NNReal) ^ (-(↑n - 1 : ℤ)) := by
        simp [WithZeroMulInt.toNNReal, WithZero.coe_ne_zero]

      have hrhs_cast : (↑(Ideal.absNorm v.asIdeal) : ℝ) ^ (-(↑n - 1 : ℤ)) =
          ↑((↑(Ideal.absNorm v.asIdeal) : NNReal) ^ (-(↑n - 1 : ℤ))) := by
        rw [NNReal.coe_zpow]; push_cast; ring
      rw [hrhs_cast] at hlt_thresh


      rw [← htoNNReal_coe] at hlt_thresh
      have hnnr_lt : WithZeroMulInt.toNNReal hne0 val_y <
          WithZeroMulInt.toNNReal hne0
            (↑(Multiplicative.ofAdd (-(↑n - 1 : ℤ)))) := by
        exact_mod_cast hlt_thresh

      have hlt_one := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal (R := 𝓞 K) v
      have hval_lt : val_y < ↑(Multiplicative.ofAdd (-(↑n - 1 : ℤ))) :=
        (WithZeroMulInt.toNNReal_strictMono hlt_one).lt_iff_lt.mp hnnr_lt

      rcases val_y with _ | a
      ·
        exact WithZero.zero_le _
      ·
        show (a : WithZero (Multiplicative ℤ)) ≤ _
        have hval_lt' : (a : WithZero (Multiplicative ℤ)) <
            ↑(Multiplicative.ofAdd (-(↑n - 1 : ℤ))) := hval_lt
        rw [WithZero.coe_lt_coe] at hval_lt'
        rw [WithZero.coe_le_coe]
        have h_add : Multiplicative.toAdd a < -(↑n - 1 : ℤ) := by
          rwa [show a = Multiplicative.ofAdd (Multiplicative.toAdd a) from (ofAdd_toAdd a).symm,
            Multiplicative.ofAdd_lt] at hval_lt'
        rw [show a = Multiplicative.ofAdd (Multiplicative.toAdd a) from (ofAdd_toAdd a).symm]
        exact Multiplicative.ofAdd_le.mpr (by omega)
    exact ⟨α_x, hsign_x, hfp_x⟩

theorem finitePartMapHom_surj_on_ker_sign (𝔪 : @Modulus K _ _)
    (u : (NumberField.RingOfIntegers K ⧸ 𝔪.finitePartIdeal)ˣ) :
    ∃ α : UnitsCoprime_subgroup' K 𝔪,
      signMapHom K 𝔪 α = 1 ∧ finitePartMapHom K 𝔪 α = u := by
  exact weak_approx_coprime_sign_finitePart 𝔪 u

theorem signTimesFinitePart_surjective (𝔪 : @Modulus K _ _) :
    Function.Surjective
      (MonoidHom.prod (signMapHom K 𝔪) (finitePartMapHom K 𝔪)) := by
  intro ⟨s, u⟩

  obtain ⟨α₁, hα₁⟩ := signMapHom_surjective 𝔪 s

  obtain ⟨α₂, hα₂_sign, hα₂_fin⟩ :=
    finitePartMapHom_surj_on_ker_sign 𝔪 (u * (finitePartMapHom K 𝔪 α₁)⁻¹)

  refine ⟨α₁ * α₂, Prod.ext ?_ ?_⟩
  ·
    show ((signMapHom K 𝔪 (α₁ * α₂)), (finitePartMapHom K 𝔪 (α₁ * α₂))).1 = s
    simp only [map_mul, hα₁, hα₂_sign, mul_one]
  ·
    show ((signMapHom K 𝔪 (α₁ * α₂)), (finitePartMapHom K 𝔪 (α₁ * α₂))).2 = u
    simp only [map_mul, hα₂_fin]
    rw [mul_comm ((finitePartMapHom K 𝔪) α₁) (u * _), mul_assoc, inv_mul_cancel,
        mul_one]

theorem finite_part_map_exists (𝔪 : @Modulus K _ _) :
    ∃ (f : UnitsCoprime_subgroup' K 𝔪 →*
        (NumberField.RingOfIntegers K ⧸ 𝔪.finitePartIdeal)ˣ),
      (∀ α : UnitsCoprime_subgroup' K 𝔪,
        f α = 1 ↔
          ∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 →
            v.valuation K (((α : Kˣ) : K) - 1) ≤
              ↑(Multiplicative.ofAdd (-(𝔪 (Place.finite v) : ℤ)))) ∧
      Function.Surjective (MonoidHom.prod (signMapHom K 𝔪) f) :=
  ⟨finitePartMapHom K 𝔪, finitePartMapHom_ker_iff 𝔪, signTimesFinitePart_surjective 𝔪⟩

theorem theorem_21_8_quotient_iso (𝔪 : @Modulus K _ _) :
    Nonempty (QuotientUnits K 𝔪 ≃* SignsTimesUnits K 𝔪) := by
  obtain ⟨f, hf_ker, hφ_surj⟩ := finite_part_map_exists 𝔪
  set φ := MonoidHom.prod (signMapHom K 𝔪) f

  have hker : φ.ker = UnitsCongruent_in_UnitsCoprime K 𝔪 := by
    rw [MonoidHom.ker_prod]
    ext ⟨α, hα_cop⟩
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker]
    constructor
    ·
      intro ⟨hsign, hfin⟩
      refine ⟨hα_cop, (hf_ker ⟨α, hα_cop⟩).mp hfin, ?_⟩
      intro w hw


      have : signMapHom K 𝔪 ⟨α, hα_cop⟩ = 1 := hsign
      have hw_mem : w ∈ 𝔪.infSupportFinset := by
        simp only [Modulus.infSupportFinset, Set.Finite.mem_toFinset,
          Set.mem_preimage, Set.mem_setOf_eq]
        exact hw
      have := congr_fun this ⟨w, hw_mem⟩
      simp only [signMapHom, MonoidHom.coe_mk, OneHom.coe_mk, Pi.one_apply] at this
      rw [ofAdd_eq_one] at this
      exact (signAtPlace_eq_zero_iff _ _).mp this
    ·
      intro ⟨_, hα_cong, hα_sign⟩
      refine ⟨?_, (hf_ker ⟨α, hα_cop⟩).mpr hα_cong⟩

      ext ⟨w, hw_mem⟩
      simp only [signMapHom, MonoidHom.coe_mk, OneHom.coe_mk, Pi.one_apply,
        toAdd_ofAdd, toAdd_one]

      exact (signAtPlace_eq_zero_iff _ _).mpr (hα_sign w (by
        simp only [Modulus.infSupportFinset, Set.Finite.mem_toFinset,
          Set.mem_preimage, Set.mem_setOf_eq] at hw_mem
        exact hw_mem))
  haveI : (UnitsCongruent_in_UnitsCoprime K 𝔪).Normal :=
    hker ▸ MonoidHom.normal_ker φ
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ_surj)⟩

end RayClassField
end
