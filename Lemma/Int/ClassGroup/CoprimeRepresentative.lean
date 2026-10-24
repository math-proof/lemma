import Mathlib
import sympy.Basic
open Ideal


/--
[Ideal.exists_isCoprime_mul_isPrincipal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ClassGroup/CoprimeRepresentative.lean)
-/
@[path]
lemma Ideal.exists_isCoprime_mul_isPrincipal
  [CommRing A] [IsDedekindDomain A]
  {I a : Ideal A}
-- given
  (hI : I ≠ ⊥)
  (ha : a ≠ ⊥) :
-- imply
  ∃ J : Ideal A, IsCoprime J a ∧ Submodule.IsPrincipal (I * J) := by
-- proof
  have hle : I * a ≤ I := Ideal.mul_le_left
  have hne : I * a ≠ ⊥ := mul_ne_zero hI ha
  obtain ⟨x, hx⟩ := IsDedekindDomain.exists_sup_span_eq hle hne
  have hx_le : Ideal.span {x} ≤ I := by rw [← hx]; exact le_sup_right
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hx_le
  refine ⟨J, ?_, ?_⟩
  · have h1 : I * (a ⊔ J) = I * ⊤ := by
    rw [Ideal.mul_sup, Ideal.mul_top, ← hJ, hx]
    have h2 : a ⊔ J = ⊤ := mul_left_cancel₀ hI h1
    exact Ideal.isCoprime_iff_sup_eq.mpr (by rw [sup_comm]; exact h2)
  · rw [← hJ]
    exact ⟨⟨x, rfl⟩⟩

/--
[ClassGroup.exists_mk0_eq_and_isCoprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ClassGroup/CoprimeRepresentative.lean)
-/
@[path]
lemma ClassGroup.exists_mk0_eq_and_isCoprime
  [CommRing A] [IsDedekindDomain A]
  {c : ClassGroup A}
  {a : Ideal A}
-- given
  (ha : a ≠ ⊥) :
-- imply
  ∃ (K : Ideal A) (hK : K ≠ ⊥),
      ClassGroup.mk0 ⟨K, mem_nonZeroDivisors_iff_ne_zero.mpr hK⟩ = c ∧
        IsCoprime K a := by
-- proof
  obtain ⟨⟨J, hJ_mem⟩, hJ_class⟩ := ClassGroup.mk0_surjective c⁻¹
  have hJ_ne : J ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp hJ_mem
  obtain ⟨K, hK_coprime, hK_principal⟩ :=
    Ideal.exists_isCoprime_mul_isPrincipal J a hJ_ne ha
  by_cases hK_ne : K = ⊥
  · have hsup := Ideal.isCoprime_iff_sup_eq.mp hK_coprime
    have ha_top : a = ⊤ := by rw [← hsup, hK_ne, bot_sup_eq]
    obtain ⟨⟨Kprime, hKprime_mem⟩, hKprime_class⟩ := ClassGroup.mk0_surjective c
    have hKprime_ne : Kprime ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp hKprime_mem
    refine ⟨Kprime, hKprime_ne, hKprime_class, ?_⟩
    exact Ideal.isCoprime_iff_sup_eq.mpr (by rw [ha_top, sup_top_eq])
  · refine ⟨K, hK_ne, ?_, hK_coprime⟩
    have hJK_ne : J * K ≠ ⊥ := mul_ne_zero hJ_ne hK_ne
    have h1 :
      ClassGroup.mk0 ⟨J * K, mem_nonZeroDivisors_iff_ne_zero.mpr hJK_ne⟩ =
        1 := by
      rwa [ClassGroup.mk0_eq_one_iff]
    have h2 :
      ClassGroup.mk0 ⟨J * K, mem_nonZeroDivisors_iff_ne_zero.mpr hJK_ne⟩ =
        ClassGroup.mk0 ⟨J, hJ_mem⟩ *
          ClassGroup.mk0 ⟨K, mem_nonZeroDivisors_iff_ne_zero.mpr hK_ne⟩ := by
      rw [← MonoidHom.map_mul]
      congr 1
    rw [h2, hJ_class] at h1
    exact (eq_of_inv_mul_eq_one h1).symm


-- created on 2026-10-20
-- updated on 2026-10-23
