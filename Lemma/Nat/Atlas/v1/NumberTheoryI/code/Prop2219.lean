import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.NumberTheoryI.code.Prop2219.Part2
open Complex Finset Section19 RayClassField
open scoped NumberField


namespace RayClassField

/--
[rayClassPartialZeta_residue_val_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2219.lean)
-/
@[path]
lemma rayClassPartialZeta_residue_val_ne_zero
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {γ : RayClassGroup K 𝔪} :
-- imply
  rayClassPartialZeta_residue_val γ ≠ 0 := by
-- proof
  unfold rayClassPartialZeta_residue_val
  apply div_ne_zero
  · exact_mod_cast NumberField.dedekindZeta_residue_ne_zero K
  · exact_mod_cast Fintype.card_ne_zero
set_option checkBinderAnnotations false in

end RayClassField

namespace RayClassField

/--
[rayClassPartialZeta_coeffs_sum_eq_count](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2219.lean)
-/
@[path]
lemma rayClassPartialZeta_coeffs_sum_eq_count
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {γ : RayClassGroup K 𝔪}
  {t : ℕ} :
-- imply
  ∑ i ∈ Finset.range t, rayClassPartialZeta_coeffs γ (i + 1) = (Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧ Ideal.absNorm I ≤ t ∧ idealInRayClass 𝔪 I = γ} : ℂ) := by
-- proof
  simp only [rayClassPartialZeta_coeffs, Nat.succ_ne_zero, ↓reduceIte]
  rw [← Nat.cast_sum]
  congr 1
  have h_absNorm_pos : ∀ (I : Ideal (𝓞 K)), I ≠ ⊥ → 1 ≤ Ideal.absNorm I := by
    intro I hI
    have := (Ideal.absNorm_eq_zero_iff.not.mpr hI)
    omega
  have h_fiber_finite : ∀ (n : ℕ),
    Finite {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧
      Ideal.absNorm I = n ∧ idealInRayClass 𝔪 I = γ} := by
    intro n
    have hfin := Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n
    haveI : Finite {I : Ideal (𝓞 K) | Ideal.absNorm I = n} := hfin.to_subtype
    exact Finite.of_injective
      (fun (x : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧
        Ideal.absNorm I = n ∧ idealInRayClass 𝔪 I = γ}) =>
        (⟨x.val, x.prop.2.2.1⟩ : {I : Ideal (𝓞 K) | Ideal.absNorm I = n}))
      (fun ⟨I₁, _⟩ ⟨I₂, _⟩ heq => by
        simp only [Subtype.mk.injEq] at heq; exact Subtype.ext heq)
  symm
  have h_equiv : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧
    Ideal.absNorm I ≤ t ∧ idealInRayClass 𝔪 I = γ} ≃
    (Σ (k : Fin t), {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧
      Ideal.absNorm I = k.val + 1 ∧ idealInRayClass 𝔪 I = γ}) :=
    { toFun := fun ⟨I, hne, hcop, hle, hclass⟩ =>
      ⟨⟨Ideal.absNorm I - 1, by have := h_absNorm_pos I hne; omega⟩,
        ⟨I, hne, hcop,
          (by have hpos := h_absNorm_pos I hne; simp only [Fin.val_mk]; omega),
          hclass⟩⟩
      invFun := fun ⟨k, I, hne, hcop, hnorm, hclass⟩ =>
        ⟨I, hne, hcop, by omega, hclass⟩
      left_inv := fun ⟨I, hne, hcop, hle, hclass⟩ => by simp
      right_inv := fun ⟨⟨k, hk⟩, ⟨I, hne, hcop, hnorm, hclass⟩⟩ => by
        simp only [Fin.val_mk] at hnorm
        have hkey : Ideal.absNorm I - 1 = k := by omega
        subst hkey
        simp }
  calc Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧
    Ideal.absNorm I ≤ t ∧ idealInRayClass 𝔪 I = γ}
    = Nat.card (Σ (k : Fin t), {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧
      Ideal.absNorm I = k.val + 1 ∧ idealInRayClass 𝔪 I = γ}) :=
      Nat.card_congr h_equiv
    _ = ∑ k : Fin t, Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧
      Ideal.absNorm I = k.val + 1 ∧ idealInRayClass 𝔪 I = γ} := by
      haveI : ∀ (a : Fin t), Finite {I : Ideal (𝓞 K) // I ≠ ⊥ ∧
        IsCoprime I 𝔪.finitePartIdeal ∧
        Ideal.absNorm I = a.val + 1 ∧ idealInRayClass 𝔪 I = γ} :=
        fun a => h_fiber_finite (a.val + 1)
      rw [Nat.card_sigma]
    _ = ∑ x ∈ Finset.range t, Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧
      Ideal.absNorm I = x + 1 ∧ idealInRayClass 𝔪 I = γ} :=
      Fin.sum_univ_eq_sum_range (fun x => Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧
        Ideal.absNorm I = x + 1 ∧ idealInRayClass 𝔪 I = γ}) t
set_option checkBinderAnnotations false in

end RayClassField

namespace RayClassField

/--
[halfPlane_exponent_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2219.lean)
-/
@[path]
lemma halfPlane_exponent_nonneg
  {K : Type u}
  [Field K]
  [NumberField K] :
-- imply
  (0 : ℝ) ≤ 1 - 1 / (Module.finrank ℚ K : ℝ) := by
-- proof
  have hn : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.mpr Module.finrank_pos
  have h1 : 1 / (Module.finrank ℚ K : ℝ) ≤ 1 := by
    rw [div_le_one hn]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp Module.finrank_pos)
  linarith

end RayClassField

namespace RayClassField

/--
[halfPlane_exponent_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2219.lean)
-/
@[path]
lemma halfPlane_exponent_lt_one
  {K : Type u}
  [Field K]
  [NumberField K] :
-- imply
  1 - 1 / (Module.finrank ℚ K : ℝ) < 1 := by
-- proof
  have hn : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.mpr Module.finrank_pos
  linarith [div_pos one_pos hn]

end RayClassField

namespace RayClassField

/--
[rayClassPartialZeta_ext_eq_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2219.lean)
-/
@[path]
lemma rayClassPartialZeta_ext_eq_decomp
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {γ : RayClassGroup K 𝔪} :
-- imply
  ∀ᶠ s in nhds (1 : ℂ), rayClassPartialZeta_ext γ s = rayClassPartialZeta_residue 𝔪 * riemannZeta s + rayClassPartialZeta_regularPart γ s := by
-- proof
  apply Filter.Eventually.of_forall
  intro s
  simp only [rayClassPartialZeta_regularPart, rayClassPartialZeta_ext,
    dirichletSeriesContinuation, rayClassPartialZeta_residue_val, rayClassPartialZeta_residue]

end RayClassField

namespace RayClassField

/--
[weberLFunction_combinedCoeffs_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2219.lean)
-/
@[path]
lemma weberLFunction_combinedCoeffs_eq_sum
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {χ : RayClassChar K 𝔪} :
-- imply
  weberLFunction_combinedCoeffs χ = ∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) • (rayClassPartialZeta_coeffs γ) := by
-- proof
  ext n
  simp [weberLFunction_combinedCoeffs, Finset.sum_apply]

end RayClassField

namespace RayClassField

/--
[evalIdealExt_eq_char_idealInRayClass](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2219.lean)
-/
@[path]
lemma evalIdealExt_eq_char_idealInRayClass
  {K : Type u}
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {χ : RayClassChar K 𝔪}
  {I : Ideal (𝓞 K)}
-- given
  (hne : I ≠ ⊥)
  (hcop : IsCoprime I 𝔪.finitePartIdeal) :
-- imply
  χ.evalIdealExt I = ↑(χ (idealInRayClass 𝔪 I)) := by
-- proof
  classical
  simp only [RayClassChar.evalIdealExt, dif_pos hcop, RayClassChar.evalIdeal]
  congr 1
  unfold idealInRayClass
  rw [dif_pos ⟨hne, hcop⟩]
  simp only [nonzeroIdealToFracIdealCoprime]

end RayClassField

namespace RayClassField

/--
[summand_fiber_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2219.lean)
-/
@[path]
lemma summand_fiber_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {χ : RayClassChar K 𝔪}
  {γ : RayClassGroup K 𝔪}
  {s : ℂ}
-- given
  (𝔞 : {I : Ideal (𝓞 K) // I ≠ ⊥})
  (hmem : idealInRayClass 𝔪 𝔞.val = γ) :
-- imply
  χ.evalIdealExt 𝔞.val * (↑(Ideal.absNorm 𝔞.val) : ℂ) ^ (-s) = if IsCoprime 𝔞.val 𝔪.finitePartIdeal then (χ γ : ℂ) * (↑(Ideal.absNorm 𝔞.val) : ℂ) ^ (-s) else 0 := by
-- proof
  split_ifs with hcop
  · rw [evalIdealExt_eq_char_idealInRayClass χ 𝔞.val 𝔞.prop hcop, hmem]
  · rw [RayClassChar.evalIdealExt_eq_zero_of_not_coprime χ 𝔞.val hcop, zero_mul]
set_option maxHeartbeats 400000 in

end RayClassField

namespace RayClassField

/--
[fiber_tsum_eq_LSeries](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2219.lean)
-/
@[path]
lemma fiber_tsum_eq_LSeries
  {K : Type u}
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {γ : RayClassGroup K 𝔪}
  {s : ℂ} :
-- imply
  ∑' (𝔞 : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧ idealInRayClass 𝔪 I = γ}), (↑(Ideal.absNorm 𝔞.val) : ℂ) ^ (-s) = LSeries (rayClassPartialZeta_coeffs γ) s := by
-- proof
  classical
  set A := {I : Ideal (𝓞 K) //
    I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧ idealInRayClass 𝔪 I = γ}
  set g : A → ℕ := fun a => Ideal.absNorm a.val
  set H : (Σ n, {a : A // g a = n}) → ℂ := fun c => (↑c.1 : ℂ) ^ (-s)
  have hHF : ∀ c, H c = (fun a : A => (↑(g a) : ℂ) ^ (-s)) ((Equiv.sigmaFiberEquiv g) c) := by
    intro ⟨n, a, ha⟩
    simp [H, Equiv.sigmaFiberEquiv, ha]
  have hLHS : ∑' (a : A), (↑(Ideal.absNorm a.val) : ℂ) ^ (-s) = ∑' c, H c := by
    rw [← Equiv.tsum_eq (Equiv.sigmaFiberEquiv g)]
    congr 1; ext c
    exact (hHF c).symm
  rw [hLHS]
  by_cases hSH : Summable H
  · rw [hSH.tsum_sigma]
    unfold LSeries
    congr 1; ext n
    by_cases hn : n = 0
    ·
      subst hn
      simp only [LSeries.term_zero]
      convert tsum_empty using 1
      rw [isEmpty_iff]
      intro ⟨⟨I, hI⟩, hgI⟩
      simp only [g] at hgI
      exact hI.1 (Ideal.absNorm_eq_zero_iff.mp hgI)
    ·
      rw [LSeries.term_of_ne_zero hn]
      haveI : Finite {a : A // g a = n} := by
        have hfin := Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n
        haveI : Finite {I : Ideal (𝓞 K) | Ideal.absNorm I = n} := hfin.to_subtype
        exact Finite.of_injective
          (fun (x : {a : A // g a = n}) =>
            (⟨x.val.val, x.prop⟩ : {I : Ideal (𝓞 K) | Ideal.absNorm I = n}))
          (fun ⟨⟨I₁, _⟩, _⟩ ⟨⟨I₂, _⟩, _⟩ heq => by
            simp only [Subtype.mk.injEq] at heq; exact Subtype.ext (Subtype.ext heq))
      haveI : Fintype {a : A // g a = n} := Fintype.ofFinite _
      rw [tsum_fintype]
      simp only [H, Finset.sum_const, nsmul_eq_mul]
      simp only [rayClassPartialZeta_coeffs, if_neg hn]
      rw [div_eq_mul_inv, cpow_neg]
      congr 1
      rw [Nat.cast_inj]
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      apply Nat.card_congr
      exact {
        toFun := fun ⟨⟨I, hne, hcop, hclass⟩, hnorm⟩ => ⟨I, hne, hcop, hnorm, hclass⟩
        invFun := fun ⟨I, hne, hcop, hnorm, hclass⟩ => ⟨⟨I, hne, hcop, hclass⟩, hnorm⟩
        left_inv := fun ⟨⟨I, hne, hcop, hclass⟩, hnorm⟩ => rfl
        right_inv := fun ⟨I, hne, hcop, hnorm, hclass⟩ => rfl
      }
  ·
    rw [tsum_eq_zero_of_not_summable hSH]
    symm
    rw [LSeries, tsum_eq_zero_of_not_summable]
    intro hLS
    apply hSH
    set f := rayClassPartialZeta_coeffs γ
    apply Summable.of_norm
    rw [show (fun c : (Σ n, {a : A // g a = n}) => ‖H c‖) =
      (fun c : (Σ n, {a : A // g a = n}) => ‖(↑c.1 : ℂ) ^ (-s)‖) from rfl]
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
    constructor
    ·
      intro n
      by_cases hn : n = 0
      ·
        subst hn
        have : IsEmpty {a : A // g a = 0} := by
          rw [isEmpty_iff]
          intro ⟨⟨I, hI⟩, hgI⟩
          simp only [g] at hgI
          exact hI.1 (Ideal.absNorm_eq_zero_iff.mp hgI)
        exact summable_of_ne_finset_zero (s := ∅) (fun x => isEmptyElim x)
      ·
        haveI : Finite {a : A // g a = n} := by
          have hfin := Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n
          haveI : Finite {I : Ideal (𝓞 K) | Ideal.absNorm I = n} := hfin.to_subtype
          exact Finite.of_injective
            (fun (x : {a : A // g a = n}) =>
              (⟨x.val.val, x.prop⟩ : {I : Ideal (𝓞 K) | Ideal.absNorm I = n}))
            (fun ⟨⟨I₁, _⟩, _⟩ ⟨⟨I₂, _⟩, _⟩ heq => by
              simp only [Subtype.mk.injEq] at heq; exact Subtype.ext (Subtype.ext heq))
        haveI : Fintype {a : A // g a = n} := Fintype.ofFinite _
        exact (hasSum_fintype _).summable
    ·
      apply Summable.of_nonneg_of_le
        (fun n => tsum_nonneg (fun _ => norm_nonneg _))
        (fun n => ?_)
        hLS.norm
      by_cases hn : n = 0
      · subst hn
        have : IsEmpty {a : A // g a = 0} := by
          rw [isEmpty_iff]
          intro ⟨⟨I, hI⟩, hgI⟩
          simp only [g] at hgI
          exact hI.1 (Ideal.absNorm_eq_zero_iff.mp hgI)
        simp [tsum_empty]
      · haveI : Finite {a : A // g a = n} := by
        have hfin := Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n
        haveI : Finite {I : Ideal (𝓞 K) | Ideal.absNorm I = n} := hfin.to_subtype
        exact Finite.of_injective
          (fun (x : {a : A // g a = n}) =>
            (⟨x.val.val, x.prop⟩ : {I : Ideal (𝓞 K) | Ideal.absNorm I = n}))
          (fun ⟨⟨I₁, _⟩, _⟩ ⟨⟨I₂, _⟩, _⟩ heq => by
            simp only [Subtype.mk.injEq] at heq; exact Subtype.ext (Subtype.ext heq))
        haveI : Fintype {a : A // g a = n} := Fintype.ofFinite _
        rw [tsum_fintype]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [LSeries.term_of_ne_zero hn, norm_div]
        rw [show ‖(↑n : ℂ) ^ s‖ = ‖(↑n : ℂ) ^ s‖ from rfl]
        rw [show ‖(↑n : ℂ) ^ (-s)‖ = (‖(↑n : ℂ) ^ s‖)⁻¹ from by
          rw [Complex.cpow_neg, norm_inv]]
        rw [div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (norm_nonneg _))
        simp only [f, rayClassPartialZeta_coeffs, if_neg hn]
        rw [Complex.norm_natCast]
        rw [Nat.cast_le]
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
        haveI : Finite { I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧ Ideal.absNorm I = n ∧ idealInRayClass 𝔪 I = γ } := by
          have hfin := Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n
          haveI : Finite {I : Ideal (𝓞 K) | Ideal.absNorm I = n} := hfin.to_subtype
          exact Finite.of_injective
            (fun (x : { I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧ Ideal.absNorm I = n ∧ idealInRayClass 𝔪 I = γ }) =>
              (⟨x.val, x.prop.2.2.1⟩ : {I : Ideal (𝓞 K) | Ideal.absNorm I = n}))
            (fun ⟨I₁, _⟩ ⟨I₂, _⟩ heq => by
              simp only [Subtype.mk.injEq] at heq; exact Subtype.ext heq)
        exact Nat.card_le_card_of_injective
          (fun ⟨⟨I, hne, hcop, hclass⟩, hnorm⟩ => ⟨I, hne, hcop, hnorm, hclass⟩)
          (fun ⟨⟨I₁, _, _, _⟩, _⟩ ⟨⟨I₂, _, _, _⟩, _⟩ heq => by
            simp only [Subtype.mk.injEq] at heq; exact Subtype.ext (Subtype.ext heq))
set_option maxHeartbeats 400000 in

end RayClassField

namespace RayClassField

/--
[dirichletSeries_eq_sum_rayClass_LSeries](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2219.lean)
-/
@[path]
lemma dirichletSeries_eq_sum_rayClass_LSeries
  {K : Type u}
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {χ : RayClassChar K 𝔪}
  {s : ℂ}
-- given
  (hs : 1 < s.re) :
-- imply
  ∑' (𝔞 : {I : Ideal (NumberField.RingOfIntegers K) // I ≠ ⊥}), χ.evalIdealExt (𝔞 : Ideal (NumberField.RingOfIntegers K)) * (↑(Ideal.absNorm (𝔞 : Ideal (NumberField.RingOfIntegers K))) : ℂ) ^ (-s) = ∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) * LSeries (rayClassPartialZeta_coeffs γ) s := by
-- proof
  classical
  set f : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℂ :=
    fun 𝔞 => χ.evalIdealExt 𝔞.val * (↑(Ideal.absNorm 𝔞.val) : ℂ) ^ (-s) with hf_def
  set fiberMap : {I : Ideal (𝓞 K) // I ≠ ⊥} → RayClassGroup K 𝔪 :=
    fun 𝔞 => idealInRayClass 𝔪 𝔞.val with hfiberMap_def
  have hHasSum := WeberLFunction_eulerProduct_hasSum K 𝔪 χ s hs
  have hFiber := hHasSum.tsum_fiberwise fiberMap
  have hLHS := hHasSum.tsum_eq
  have hRHS := hFiber.tsum_eq
  rw [tsum_fintype] at hRHS
  rw [hLHS, ← hRHS]
  congr 1
  ext γ
  show ∑' (𝔞 : ↑(fiberMap ⁻¹' {γ})), f (𝔞 : {I : Ideal (𝓞 K) // I ≠ ⊥}) =
    (χ γ : ℂ) * LSeries (rayClassPartialZeta_coeffs γ) s
  simp only [hf_def]
  have hterm_eq : ∀ (𝔞 : ↑(fiberMap ⁻¹' {γ})),
    χ.evalIdealExt 𝔞.val.val * (↑(Ideal.absNorm 𝔞.val.val) : ℂ) ^ (-s) =
    if IsCoprime (𝔞.val.val : Ideal (𝓞 K)) 𝔪.finitePartIdeal
    then (χ γ : ℂ) * (↑(Ideal.absNorm 𝔞.val.val) : ℂ) ^ (-s)
    else 0 := by
    intro ⟨𝔞, h𝔞⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h𝔞
    exact summand_fiber_eq χ γ s 𝔞 h𝔞
  simp_rw [hterm_eq]
  set S : Set ↑(fiberMap ⁻¹' {γ}) :=
    {𝔞 | IsCoprime (𝔞.val.val : Ideal (𝓞 K)) 𝔪.finitePartIdeal}
  have hind : ∀ 𝔞, (if IsCoprime (𝔞.val.val : Ideal (𝓞 K)) 𝔪.finitePartIdeal
    then (χ γ : ℂ) * (↑(Ideal.absNorm (𝔞.val.val : Ideal (𝓞 K))) : ℂ) ^ (-s)
    else 0) =
    S.indicator (fun 𝔞 => (χ γ : ℂ) *
      (↑(Ideal.absNorm (𝔞.val.val : Ideal (𝓞 K))) : ℂ) ^ (-s)) 𝔞 := by
    intro 𝔞; simp [Set.indicator_apply, S]
  simp_rw [hind]
  rw [← _root_.tsum_subtype S (fun (𝔞 : ↑(fiberMap ⁻¹' {γ})) => (χ γ : ℂ) *
    (↑(Ideal.absNorm (𝔞.val.val : Ideal (𝓞 K))) : ℂ) ^ (-s))]
  simp_rw [tsum_mul_left]
  congr 1
  rw [← fiber_tsum_eq_LSeries γ s]
  let A := {I : Ideal (𝓞 K) //
    I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧ idealInRayClass 𝔪 I = γ}
  let hequiv : ↑S ≃ A := {
    toFun := fun ⟨⟨⟨I, hne⟩, hfib⟩, hcop⟩ => ⟨I, hne, hcop, by
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hfiberMap_def] at hfib; exact hfib⟩
    invFun := fun ⟨I, hne, hcop, hfib⟩ => ⟨⟨⟨I, hne⟩, by
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hfiberMap_def]; exact hfib⟩, hcop⟩
    left_inv := fun ⟨⟨⟨I, hne⟩, hfib⟩, hcop⟩ => rfl
    right_inv := fun ⟨I, hne, hcop, hfib⟩ => rfl
  }
  exact Equiv.tsum_eq hequiv (fun a => (↑(Ideal.absNorm a.val) : ℂ) ^ (-s))

end RayClassField

namespace RayClassField

/--
[sum_nonprincipal_char_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2219.lean)
-/
@[path]
lemma sum_nonprincipal_char_eq_zero
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {χ : RayClassChar K 𝔪}
-- given
  (hχ : ¬χ.IsPrincipal) :
-- imply
  ∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) = 0 := by
-- proof
  simp only [RayClassChar.IsPrincipal, not_forall] at hχ
  obtain ⟨g₀, hg₀⟩ := hχ
  have key : (χ g₀ : ℂ) * ∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) =
    ∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) := by
    rw [Finset.mul_sum]
    have heq : (fun γ : RayClassGroup K 𝔪 => (χ g₀ : ℂ) * (χ γ : ℂ)) =
      (fun γ : RayClassGroup K 𝔪 => (χ (g₀ * γ) : ℂ)) := by
      ext γ
      simp only [map_mul, Units.val_mul]
    rw [heq]
    exact Fintype.sum_bijective (fun γ => g₀ * γ) (Group.mulLeft_bijective g₀) _ _ (fun γ => rfl)
  have hne : (χ g₀ : ℂ) ≠ 1 := by
    intro h
    apply hg₀
    exact Units.ext h
  have hsub : ((χ g₀ : ℂ) - 1) * ∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) = 0 := by
    rw [sub_mul, one_mul, key, sub_self]
  exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hne)

end RayClassField


-- created on 2026-10-23
