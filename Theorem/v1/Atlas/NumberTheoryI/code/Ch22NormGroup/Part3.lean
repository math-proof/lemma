/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22NormGroup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part28
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.RayClassFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.ValuationBijection
import Theorem.v1.Atlas.NumberTheoryI.code.ValuationBijection
import Def.v1.Atlas.NumberTheoryI.code.Ch22NormGroup.Part3


noncomputable section

open scoped NumberField

open Classical

namespace RayClassField

universe u

theorem ramificationIndex'_pos (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    0 < ramificationIndex' K L 𝔮 := by
  unfold ramificationIndex'
  apply Nat.pos_of_ne_zero
  have hp : (lyingUnder K L 𝔮).asIdeal ≠ ⊥ := (lyingUnder K L 𝔮).ne_bot
  have hlo : 𝔮.asIdeal.LiesOver (lyingUnder K L 𝔮).asIdeal := by
    rw [Ideal.liesOver_iff]
    rw [lyingUnder, IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
  haveI := hlo
  haveI := 𝔮.isPrime
  exact Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver 𝔮.asIdeal hp

set_option maxHeartbeats 1600000 in
theorem norm_trivialValuation_of_all_lying_over (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsGalois K L]
    (x : L) (v : FinitePlace K)
    (hx : x ≠ 0)
    (hw : ∀ w : FinitePlace L, lyingUnder K L w = v →
      IsDedekindDomain.HeightOneSpectrum.valuation L w x = 1) :
    IsDedekindDomain.HeightOneSpectrum.valuation K v (Algebra.norm K x) = 1 := by
  open IsDedekindDomain in

  haveI : v.asIdeal.IsPrime := v.isPrime
  obtain ⟨Q, _, hQ_prime, hQ_over⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral
      (R := 𝓞 K) (S := 𝓞 L) v.asIdeal (⊥ : Ideal (𝓞 L)) (by simp)
  have hQ_ne_bot : Q ≠ ⊥ := by
    intro h
    rw [h, Ideal.comap_bot_of_injective (algebraMap (𝓞 K) (𝓞 L))
      (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))] at hQ_over
    exact v.ne_bot hQ_over.symm

  let w₀ : FinitePlace L := ⟨Q, hQ_prime, hQ_ne_bot⟩
  have hw₀_lies : w₀.asIdeal.LiesOver v.asIdeal := by
    exact Ideal.LiesOver.mk hQ_over.symm
  have hw₀_over : lyingUnder K L w₀ = v := by
    haveI := hw₀_lies; ext1; exact (Ideal.over_def w₀.asIdeal v.asIdeal).symm


  have hw₀_ext : ExtendsValuation (𝓞 K) K L v (w₀.valuation L) :=
    valuation_extends_of_liesOver (𝓞 K) K L (𝓞 L) v w₀ hw₀_lies

  have hσx : ∀ σ : L ≃ₐ[K] L, w₀.valuation L (σ x) = 1 := by
    intro σ
    let w_σ : Valuation L (WithZero (Multiplicative ℤ)) :=
      (w₀.valuation L).comap σ.toRingEquiv.toRingHom
    have hw_σ_ext : ExtendsValuation (𝓞 K) K L v w_σ := by
      unfold ExtendsValuation w_σ
      show ((w₀.valuation L).comap σ.toRingEquiv.toRingHom).comap (algebraMap K L) |>.IsEquiv _
      have hcomp : σ.toRingEquiv.toRingHom.comp (algebraMap K L) = algebraMap K L := by
        ext k; simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
        exact σ.commutes k
      rw [← Valuation.comap_comp, hcomp]
      exact hw₀_ext
    obtain ⟨w', hw'_above, hw'_equiv⟩ :=
      valuation_surjective_of_extends (𝓞 K) K L (𝓞 L) v w_σ hw_σ_ext
    have hw'_lyingUnder : lyingUnder K L w' = v := by
      haveI : w'.asIdeal.LiesOver v.asIdeal := hw'_above
      ext1; exact (Ideal.over_def w'.asIdeal v.asIdeal).symm
    have hw'_val : w'.valuation L x = 1 := hw w' hw'_lyingUnder


    have : w_σ x = 1 := (hw'_equiv.eq_one_iff_eq_one).mp hw'_val

    exact this

  have hnorm_prod : algebraMap K L (Algebra.norm K x) = ∏ σ : L ≃ₐ[K] L, σ x :=
    Algebra.norm_eq_prod_automorphisms K x
  have hval_norm : w₀.valuation L (algebraMap K L (Algebra.norm K x)) = 1 := by
    rw [hnorm_prod, map_prod]
    simp only [hσx, Finset.prod_const_one]

  exact hw₀_ext.eq_one_iff_eq_one.mp hval_norm

theorem fracIdeal_exists_simultaneous_trivialValuation_finset
    {L : Type u} [Field L] [NumberField L]
    (I : (FracIdeal L)ˣ) (S : Finset (FinitePlace L))
    (hI : ∀ w ∈ S, HasTrivialValuation I w) :
    ∃ x ∈ (I : FracIdeal L), x ≠ 0 ∧
      ∀ w ∈ S, IsDedekindDomain.HeightOneSpectrum.valuation L w x = 1 := by
  induction S using Finset.induction with
  | empty =>
    have hbot := FractionalIdeal.coeToSubmodule_ne_bot.mpr (Units.ne_zero I)
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    exact ⟨x, hx, hx0, fun w hw => absurd hw (Finset.notMem_empty w)⟩
  | @insert w₀ S' hw₀ ih =>
    have hI_w₀ : HasTrivialValuation I w₀ := hI w₀ (Finset.mem_insert_self w₀ S')
    obtain ⟨x₀, hx₀_mem, hx₀_val⟩ := hI_w₀
    have hI_S' : ∀ w ∈ S', HasTrivialValuation I w :=
      fun w hw => hI w (Finset.mem_insert_of_mem hw)
    obtain ⟨x₁, hx₁_mem, hx₁_ne, hx₁_val⟩ := ih hI_S'
    have hx₀_ne : x₀ ≠ 0 := by
      intro h; rw [h, map_zero] at hx₀_val; exact zero_ne_one hx₀_val


    have hv₀ : IsDedekindDomain.HeightOneSpectrum.valuation L w₀ x₁ ≠ 0 := by
      rwa [Valuation.ne_zero_iff]
    obtain ⟨Na, hNa⟩ : ∃ N : ℕ, WithZero.exp (-(N : ℤ)) *
        IsDedekindDomain.HeightOneSpectrum.valuation L w₀ x₁ < 1 := by
      obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.mp hv₀
      refine ⟨(Multiplicative.toAdd m + 1).toNat, ?_⟩
      rw [← hm]
      simp only [WithZero.exp]
      rw [← WithZero.coe_mul,
        show (1 : WithZero (Multiplicative ℤ)) = ↑(1 : Multiplicative ℤ) from rfl,
        WithZero.coe_lt_coe,
        show m = Multiplicative.ofAdd (Multiplicative.toAdd m) from (ofAdd_toAdd m).symm,
        ← ofAdd_add,
        show (1 : Multiplicative ℤ) = Multiplicative.ofAdd 0 from rfl,
        Multiplicative.ofAdd_lt]
      simp only [ofAdd_toAdd]
      omega

    have hv_S' : ∀ w ∈ S', ∃ N : ℕ, WithZero.exp (-(N : ℤ)) *
        IsDedekindDomain.HeightOneSpectrum.valuation L w x₀ < 1 := by
      intro w _
      have hwne : IsDedekindDomain.HeightOneSpectrum.valuation L w x₀ ≠ 0 := by
        rwa [Valuation.ne_zero_iff]
      obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.mp hwne
      refine ⟨(Multiplicative.toAdd m + 1).toNat, ?_⟩
      rw [← hm]
      simp only [WithZero.exp]
      rw [← WithZero.coe_mul,
        show (1 : WithZero (Multiplicative ℤ)) = ↑(1 : Multiplicative ℤ) from rfl,
        WithZero.coe_lt_coe,
        show m = Multiplicative.ofAdd (Multiplicative.toAdd m) from (ofAdd_toAdd m).symm,
        ← ofAdd_add,
        show (1 : Multiplicative ℤ) = Multiplicative.ofAdd 0 from rfl,
        Multiplicative.ofAdd_lt]
      simp only [ofAdd_toAdd]
      omega


    let Nb := S'.sup (fun w => if h : w ∈ S' then (hv_S' w h).choose else 0)
    let N := max Na (max Nb 1)

    have hN_ge_Na : Na ≤ N := le_max_left _ _
    have hN_ge_Nb : Nb ≤ N := le_trans (le_max_left _ _) (le_max_right _ _)
    have hN_pos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) (le_max_right _ _))

    have hcop : IsCoprime (w₀.asIdeal ^ N) (⨅ w ∈ S', w.asIdeal ^ N) := by
      apply Ideal.isCoprime_biInf
      intro w hw
      exact (IsDedekindDomain.HeightOneSpectrum.isCoprime_of_ne w₀ w
        (fun h => hw₀ (h ▸ hw))).pow
    obtain ⟨a, ha, b, hb, hab⟩ := hcop.exists


    set c := a with hc_def
    have hc_mem : c ∈ w₀.asIdeal ^ N := ha
    have hb_mem : ∀ w ∈ S', b ∈ w.asIdeal ^ N := by
      intro w hw
      exact (Ideal.mem_iInf.mp (Ideal.mem_iInf.mp hb w)) hw
    have h1mc : 1 - c = b := by rw [← hab]; ring

    let x : L := (algebraMap (𝓞 L) L b) * x₀ + (algebraMap (𝓞 L) L c) * x₁
    refine ⟨x, ?_, ?_⟩

    · show x ∈ (I : FracIdeal L)
      have hsmul₀ : (algebraMap (𝓞 L) L b) * x₀ ∈ (↑I : FracIdeal L) := by
        rw [← Algebra.smul_def]
        exact (↑I : FracIdeal L).val.smul_mem b hx₀_mem
      have hsmul₁ : (algebraMap (𝓞 L) L c) * x₁ ∈ (↑I : FracIdeal L) := by
        rw [← Algebra.smul_def]
        exact (↑I : FracIdeal L).val.smul_mem c hx₁_mem
      exact (↑I : FracIdeal L).val.add_mem hsmul₀ hsmul₁

    have hc_in_w₀ : c ∈ w₀.asIdeal := by
      exact Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp hN_pos) hc_mem
    have hb_notin_w₀ : b ∉ w₀.asIdeal := by
      intro hb'
      have h1 : (1 : 𝓞 L) ∈ w₀.asIdeal := by
        have : c + b = 1 := hab
        rw [← this]; exact w₀.asIdeal.add_mem hc_in_w₀ hb'
      exact absurd (Ideal.eq_top_of_isUnit_mem w₀.asIdeal h1 isUnit_one) w₀.isPrime.ne_top
    have hc_notin_S' : ∀ w ∈ S', c ∉ w.asIdeal := by
      intro w hw hcw
      have hb_in_w : b ∈ w.asIdeal :=
        Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp hN_pos) (hb_mem w hw)
      have h1 : (1 : 𝓞 L) ∈ w.asIdeal := by
        have : c + b = 1 := hab
        rw [← this]; exact w.asIdeal.add_mem hcw hb_in_w
      exact absurd (Ideal.eq_top_of_isUnit_mem w.asIdeal h1 isUnit_one) w.isPrime.ne_top

    have val_unit_mul : ∀ (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (r : 𝓞 L) (y : L),
        r ∉ w.asIdeal →
        IsDedekindDomain.HeightOneSpectrum.valuation L w (algebraMap (𝓞 L) L r * y) =
          IsDedekindDomain.HeightOneSpectrum.valuation L w y := by
      intro w r y hr
      rw [Valuation.map_mul, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr hr, one_mul]

    have val_small_mul : ∀ (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (r : 𝓞 L) (y : L)
        (M : ℕ),
        r ∈ w.asIdeal ^ M →
        WithZero.exp (-(M : ℤ)) * IsDedekindDomain.HeightOneSpectrum.valuation L w y < 1 →
        IsDedekindDomain.HeightOneSpectrum.valuation L w (algebraMap (𝓞 L) L r * y) < 1 := by
      intro w r y M hrM hlt
      rw [Valuation.map_mul, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      calc w.intValuation r * IsDedekindDomain.HeightOneSpectrum.valuation L w y
          ≤ WithZero.exp (-(M : ℤ)) * IsDedekindDomain.HeightOneSpectrum.valuation L w y := by
            apply mul_le_mul_left
            rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd]
            exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hrM)
        _ < 1 := hlt

    have hNa_cond : WithZero.exp (-(N : ℤ)) *
        IsDedekindDomain.HeightOneSpectrum.valuation L w₀ x₁ < 1 := by
      calc WithZero.exp (-(N : ℤ)) * IsDedekindDomain.HeightOneSpectrum.valuation L w₀ x₁
          ≤ WithZero.exp (-(Na : ℤ)) * IsDedekindDomain.HeightOneSpectrum.valuation L w₀ x₁ := by
            apply mul_le_mul_left
            exact WithZero.exp_le_exp.mpr (by omega)
        _ < 1 := hNa

    have hNb_cond : ∀ w ∈ S', WithZero.exp (-(N : ℤ)) *
        IsDedekindDomain.HeightOneSpectrum.valuation L w x₀ < 1 := by
      intro w hw
      have hNw := (hv_S' w hw).choose_spec
      have hNw_le : (hv_S' w hw).choose ≤ N := by
        have h2 := Finset.le_sup (f := fun w => if h : w ∈ S' then (hv_S' w h).choose else 0) hw
        simp only [dif_pos hw] at h2
        linarith
      calc WithZero.exp (-(N : ℤ)) * IsDedekindDomain.HeightOneSpectrum.valuation L w x₀
          ≤ WithZero.exp (-((hv_S' w hw).choose : ℤ)) *
              IsDedekindDomain.HeightOneSpectrum.valuation L w x₀ := by
            apply mul_le_mul_left
            exact WithZero.exp_le_exp.mpr (by omega)
        _ < 1 := hNw

    have hw₀_val : IsDedekindDomain.HeightOneSpectrum.valuation L w₀ x = 1 := by
      show IsDedekindDomain.HeightOneSpectrum.valuation L w₀
        ((algebraMap (𝓞 L) L b) * x₀ + (algebraMap (𝓞 L) L c) * x₁) = 1
      have hterm₁ : IsDedekindDomain.HeightOneSpectrum.valuation L w₀
          ((algebraMap (𝓞 L) L b) * x₀) = 1 := by
        rw [val_unit_mul w₀ b x₀ hb_notin_w₀]; exact hx₀_val
      have hterm₂_lt : IsDedekindDomain.HeightOneSpectrum.valuation L w₀
          ((algebraMap (𝓞 L) L c) * x₁) < 1 :=
        val_small_mul w₀ c x₁ N hc_mem hNa_cond
      rw [← hterm₁] at hterm₂_lt
      rw [add_comm]
      exact (Valuation.map_add_eq_of_lt_right
        (IsDedekindDomain.HeightOneSpectrum.valuation L w₀) hterm₂_lt).trans hterm₁

    have hS'_val : ∀ w ∈ S', IsDedekindDomain.HeightOneSpectrum.valuation L w x = 1 := by
      intro w hw
      show IsDedekindDomain.HeightOneSpectrum.valuation L w
        ((algebraMap (𝓞 L) L b) * x₀ + (algebraMap (𝓞 L) L c) * x₁) = 1
      have hterm₂ : IsDedekindDomain.HeightOneSpectrum.valuation L w
          ((algebraMap (𝓞 L) L c) * x₁) = 1 := by
        rw [val_unit_mul w c x₁ (hc_notin_S' w hw)]; exact hx₁_val w hw
      have hterm₁_lt : IsDedekindDomain.HeightOneSpectrum.valuation L w
          ((algebraMap (𝓞 L) L b) * x₀) < 1 :=
        val_small_mul w b x₀ N (hb_mem w hw) (hNb_cond w hw)
      rw [← hterm₂] at hterm₁_lt
      exact (Valuation.map_add_eq_of_lt_right
        (IsDedekindDomain.HeightOneSpectrum.valuation L w) hterm₁_lt).trans hterm₂

    exact ⟨fun hx_zero => by rw [hx_zero, map_zero] at hw₀_val; exact zero_ne_one hw₀_val,
      fun w hw_ins => by
        rcases Finset.mem_insert.mp hw_ins with rfl | hw
        · exact hw₀_val
        · exact hS'_val w hw⟩

theorem exists_simultaneous_trivialValuation (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsGalois K L]
    (I : (FracIdeal L)ˣ) (v : FinitePlace K)
    (hI : ∀ w : FinitePlace L, lyingUnder K L w = v → HasTrivialValuation I w) :
    ∃ x ∈ (I : FracIdeal L), x ≠ 0 ∧
      ∀ w : FinitePlace L, lyingUnder K L w = v →
        IsDedekindDomain.HeightOneSpectrum.valuation L w x = 1 := by
  have hfin := fiber_under_finite K L v
  let S := hfin.toFinset
  have hS : ∀ w ∈ S, HasTrivialValuation I w := by
    intro w hw
    exact hI w ((Set.Finite.mem_toFinset hfin).mp hw)
  obtain ⟨x, hxI, hx0, hxv⟩ := fracIdeal_exists_simultaneous_trivialValuation_finset I S hS
  exact ⟨x, hxI, hx0, fun w hw => hxv w ((Set.Finite.mem_toFinset hfin).mpr hw)⟩

theorem norm_mem_fracRelNorm (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsGalois K L]
    (I : FracIdeal L) (x : L) (hx : x ∈ I) :
    Algebra.norm K x ∈ (fracRelNorm K L I : FracIdeal K) := by

  show Algebra.norm K x ∈
    ↑(Ideal.relNorm (𝓞 K) I.num) *
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
        ((algebraMap (𝓞 K) K) (Algebra.intNorm (𝓞 K) (𝓞 L) I.den))⁻¹

  have hden := FractionalIdeal.den_mul_self_eq_num' (nonZeroDivisors (𝓞 L)) L I

  have hdenx : (algebraMap (𝓞 L) L) ↑I.den * x ∈
      (↑I.num : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) := by
    rw [← hden]
    exact FractionalIdeal.mul_mem_mul
      ((FractionalIdeal.mem_spanSingleton _).mpr ⟨1, one_smul _ _⟩) hx

  rw [FractionalIdeal.mem_coeIdeal] at hdenx
  obtain ⟨y, hy, hxy⟩ := hdenx

  have hny : Algebra.intNorm (𝓞 K) (𝓞 L) y ∈ Ideal.relNorm (𝓞 K) I.num := by
    rw [← Ideal.spanNorm_eq]
    exact Ideal.intNorm_mem_spanNorm (𝓞 K) hy

  have hmem1 : (algebraMap (𝓞 K) K) (Algebra.intNorm (𝓞 K) (𝓞 L) y) ∈
      (↑(Ideal.relNorm (𝓞 K) I.num) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
    (FractionalIdeal.mem_coeIdeal _).mpr ⟨_, hny, rfl⟩

  have hmem2 : ((algebraMap (𝓞 K) K) (Algebra.intNorm (𝓞 K) (𝓞 L) I.den))⁻¹ ∈
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
        ((algebraMap (𝓞 K) K) (Algebra.intNorm (𝓞 K) (𝓞 L) I.den))⁻¹ :=
    (FractionalIdeal.mem_spanSingleton _).mpr ⟨1, one_smul _ _⟩

  have hprod := FractionalIdeal.mul_mem_mul hmem1 hmem2

  suffices h : Algebra.norm K x =
      (algebraMap (𝓞 K) K) (Algebra.intNorm (𝓞 K) (𝓞 L) y) *
        ((algebraMap (𝓞 K) K) (Algebra.intNorm (𝓞 K) (𝓞 L) I.den))⁻¹ by
    rw [h]; exact hprod

  have h1 : (algebraMap (𝓞 K) K) (Algebra.intNorm (𝓞 K) (𝓞 L) y) =
      Algebra.norm K ((algebraMap (𝓞 L) L) y) :=
    Algebra.algebraMap_intNorm y
  set d : 𝓞 L := (↑I.den : 𝓞 L) with hd_def
  have h2 : (algebraMap (𝓞 K) K) (Algebra.intNorm (𝓞 K) (𝓞 L) d) =
      Algebra.norm K ((algebraMap (𝓞 L) L) d) :=
    Algebra.algebraMap_intNorm d


  have h3 : Algebra.norm K ((algebraMap (𝓞 L) L) y) =
      Algebra.norm K ((algebraMap (𝓞 L) L) d) * Algebra.norm K x := by
    rw [hxy, map_mul]
  rw [h1, h3, ← h2, mul_assoc, mul_comm (Algebra.norm K x),
    ← mul_assoc, mul_inv_cancel₀ (algMap_intNorm_den_ne_zero K L I), one_mul]

theorem hasTrivialValuation_fracIdealNorm (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsGalois K L]
    (I : (FracIdeal L)ˣ) (v : FinitePlace K)
    (hI : ∀ w : FinitePlace L, lyingUnder K L w = v → HasTrivialValuation I w) :
    HasTrivialValuation (fracIdealNorm K L I) v := by

  obtain ⟨x, hxI, hx_ne, hx_val⟩ := exists_simultaneous_trivialValuation K L I v hI

  have h_mem : Algebra.norm K x ∈ (fracRelNorm K L I.val : FracIdeal K) :=
    norm_mem_fracRelNorm K L I.val x hxI

  have h_val : IsDedekindDomain.HeightOneSpectrum.valuation K v (Algebra.norm K x) = 1 :=
    norm_trivialValuation_of_all_lying_over K L x v hx_ne hx_val

  unfold HasTrivialValuation fracIdealNorm
  rw [Units.coe_map]
  exact ⟨Algebra.norm K x, h_mem, h_val⟩

theorem fracIdealNorm_coprime (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔪 : Modulus K) (I : (FracIdeal L)ˣ)
    (hI : I ∈ FracIdealsCoprime_subgroup L (extendModulus K L 𝔪)) :
    fracIdealNorm K L I ∈ FracIdealsCoprime_subgroup K 𝔪 := by


  intro v hv


  have hram : ∀ w : FinitePlace L, lyingUnder K L w = v →
      (extendModulus K L 𝔪).toFun (Place.finite w) ≠ 0 := by
    intro w hw
    simp only [extendModulus]
    rw [hw]
    exact Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp (ramificationIndex'_pos K L w)) hv
  constructor
  ·
    exact hasTrivialValuation_fracIdealNorm K L I v
      (fun w hw => (hI w (hram w hw)).1)
  ·

    rw [show (fracIdealNorm K L I)⁻¹ = fracIdealNorm K L I⁻¹ from
      (map_inv (fracIdealNorm K L) I).symm]
    exact hasTrivialValuation_fracIdealNorm K L I⁻¹ v
      (fun w hw => (hI w (hram w hw)).2)

end RayClassField
end
