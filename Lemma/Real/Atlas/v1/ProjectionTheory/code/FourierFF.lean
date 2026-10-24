import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProjectionTheory.code.FourierFF
open Finset hiding card Fintype (card) FourierFF
open Fintype (card)
open scoped BigOperators


namespace FourierFF

/--
[fourierChar_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FourierFF.lean)
-/
@[path]
lemma fourierChar_apply
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {d : ℕ}
  {e : AddChar F ℂ}
  {ξ x : Fin d → F} :
-- imply
  fourierChar e ξ x = e (∑ i, x i * ξ i) :=
-- proof
  rfl

end FourierFF

namespace FourierFF

/--
[dft_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FourierFF.lean)
-/
@[path]
lemma dft_apply
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {d : ℕ}
  {e : AddChar F ℂ}
  {f : (Fin d → F) → ℂ}
  {ξ : Fin d → F} :
-- imply
  dft e f ξ = ∑ x, f x * e (-(∑ i, x i * ξ i)) := by
-- proof
  simp [dft, fourierChar, dotProd, AddChar.inv_apply]

end FourierFF

namespace FourierFF

/--
[fourierChar_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FourierFF.lean)
-/
@[path]
lemma fourierChar_eq_zero_iff
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {d : ℕ}
  {e : AddChar F ℂ}
  {a : Fin d → F}
-- given
  (he : e ≠ 0) :
-- imply
  fourierChar e a = 0 ↔ a = 0 := by
-- proof
  have h01 : (0 : AddChar F ℂ) = 1 := by ext x; simp
  have he1 : e ≠ 1 := by rwa [← h01]
  have hprim := AddChar.IsPrimitive.of_ne_one he1
  constructor
  · intro h0
    rw [show (0 : AddChar (Fin d → F) ℂ) = 1 from by ext x; simp] at h0
    funext i
    have key : AddChar.mulShift e (a i) = 1 := by
      ext t
      have := DFunLike.ext_iff.mp h0 (fun j => if j = i then t else 0)
      simp only [fourierChar, AddChar.compAddMonoidHom_apply, dotProd,
        AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddChar.one_apply] at this
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
      rwa [AddChar.mulShift_apply, mul_comm]
    by_contra hai
    exact (hprim hai) key
  · intro ha; subst ha; ext ξ; simp [fourierChar, dotProd]

end FourierFF

namespace FourierFF

/--
[sum_fourierChar](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FourierFF.lean)
-/
@[path]
lemma sum_fourierChar
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {d : ℕ}
  {e : AddChar F ℂ}
  {a : Fin d → F}
-- given
  (he : e ≠ 0) :
-- imply
  ∑ ξ, fourierChar e a ξ = if a = 0 then (card (Fin d → F) : ℂ) else 0 := by
-- proof
  by_cases ha : a = 0
  · subst ha; simp [fourierChar, dotProd]
  · rw [if_neg ha]
    exact AddChar.sum_eq_zero_iff_ne_zero.mpr ((fourierChar_eq_zero_iff e he a).not.mpr ha)

end FourierFF

namespace FourierFF

/--
[fourier_inversion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FourierFF.lean)
-/
@[path]
lemma fourier_inversion
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {d : ℕ}
  {e : AddChar F ℂ}
  {f : (Fin d → F) → ℂ}
  {x : Fin d → F}
-- given
  (he : e ≠ 0) :
-- imply
  f x = (↑(card (Fin d → F)))⁻¹ * ∑ ξ, dft e f ξ * fourierChar e ξ x := by
-- proof
  simp only [dft]
  have step1 : ∑ ξ, (∑ y, f y * (fourierChar e ξ)⁻¹ y) * fourierChar e ξ x =
    ∑ y, f y * (∑ ξ, (fourierChar e ξ)⁻¹ y * fourierChar e ξ x) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  rw [step1]
  have step2 : ∀ y, ∑ ξ, (fourierChar e ξ)⁻¹ y * fourierChar e ξ x =
    ∑ ξ, fourierChar e ξ (x - y) := by
    intro y; congr 1; ext ξ
    simp only [fourierChar, AddChar.compAddMonoidHom_apply, AddChar.inv_apply,
      dotProd, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_neg]
    rw [← AddChar.map_add_eq_mul]
    congr 1
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]; ring
  simp_rw [step2]
  have step3 : ∀ y, ∑ ξ, fourierChar e ξ (x - y) = ∑ ξ, fourierChar e (x - y) ξ := by
    intro y; congr 1; ext ξ
    simp only [fourierChar, AddChar.compAddMonoidHom_apply, dotProd,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    congr 1; apply Finset.sum_congr rfl; intros; ring
  simp_rw [step3]
  simp_rw [sum_fourierChar e he]
  simp only [sub_eq_zero, mul_ite, mul_zero, @eq_comm _ x]
  rw [Finset.sum_ite_eq' Finset.univ x]
  simp only [Finset.mem_univ, ite_true]
  have hcard : (card (Fin d → F) : ℂ) ≠ 0 := by
    have : 0 < card (Fin d → F) := Fintype.card_pos
    exact_mod_cast this.ne'
  field_simp

end FourierFF


-- created on 2026-10-23
