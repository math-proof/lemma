import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProjectionTheory.code.FourierFF
import Lemma.Real.Atlas.v1.ProjectionTheory.code.FourierFF
open Finset hiding card Fintype (card)
open Fintype (card)
open scoped BigOperators ComplexConjugate


namespace FourierFF

/--
[conj_dft](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/ParsevalFF.lean)
-/
@[path]
lemma conj_dft
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {d : ℕ}
  {e : AddChar (ZMod p) ℂ}
  {g : (Fin d → ZMod p) → ℂ}
  {ξ : Fin d → ZMod p} :
-- imply
  starRingEnd ℂ (dft e g ξ) = ∑ y, starRingEnd ℂ (g y) * fourierChar e ξ y := by
-- proof
  simp only [dft]
  rw [map_sum]
  congr 1; ext y
  rw [map_mul]
  congr 1
  rw [AddChar.inv_apply, fourierChar_apply, fourierChar_apply]
  rw [← AddChar.map_neg_eq_conj]
  congr 1
  simp [neg_mul, ← Finset.sum_neg_distrib]

end FourierFF

namespace FourierFF

/--
[inv_mul_fourierChar](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/ParsevalFF.lean)
-/
@[path]
lemma inv_mul_fourierChar
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {d : ℕ}
  {e : AddChar (ZMod p) ℂ}
  {ξ x y : Fin d → ZMod p} :
-- imply
  (fourierChar e ξ)⁻¹ x * fourierChar e ξ y = fourierChar e ξ (y - x) := by
-- proof
  simp only [fourierChar, AddChar.compAddMonoidHom_apply, AddChar.inv_apply,
    dotProd, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_neg]
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  ring

end FourierFF

namespace FourierFF

/--
[fourierChar_swap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/ParsevalFF.lean)
-/
@[path]
lemma fourierChar_swap
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {d : ℕ}
  {e : AddChar (ZMod p) ℂ}
  {a ξ : Fin d → ZMod p} :
-- imply
  fourierChar e ξ a = fourierChar e a ξ := by
-- proof
  simp only [fourierChar_apply]
  congr 1
  apply Finset.sum_congr rfl; intros; ring

end FourierFF

namespace FourierFF

/--
[parseval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/ParsevalFF.lean)
-/
@[path]
lemma parseval
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {d : ℕ}
  {e : AddChar (ZMod p) ℂ}
  {f g : (Fin d → ZMod p) → ℂ}
-- given
  (he : e ≠ 0) :
-- imply
  ∑ x, f x * starRingEnd ℂ (g x) = (↑(card (Fin d → ZMod p)))⁻¹ * ∑ ξ, dft e f ξ * starRingEnd ℂ (dft e g ξ) := by
-- proof
  simp_rw [conj_dft]
  simp only [dft]
  have key : ∀ x y : Fin d → ZMod p,
    ∑ ξ, (fourierChar e ξ)⁻¹ x * fourierChar e ξ y =
      if y = x then (card (Fin d → ZMod p) : ℂ) else 0 := by
    intro x y
    simp_rw [inv_mul_fourierChar, fourierChar_swap e (y - x)]
    rw [sum_fourierChar e he]
    simp [sub_eq_zero]
  have expand_rhs :
    (↑(card (Fin d → ZMod p)))⁻¹ *
      ∑ ξ : Fin d → ZMod p, (∑ x, f x * (fourierChar e ξ)⁻¹ x) *
        (∑ y, starRingEnd ℂ (g y) * fourierChar e ξ y) =
    (↑(card (Fin d → ZMod p)))⁻¹ *
      ∑ x, ∑ y, f x * starRingEnd ℂ (g y) *
        (∑ ξ, (fourierChar e ξ)⁻¹ x * fourierChar e ξ y) := by
    congr 1
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1; ext x
    rw [Finset.sum_comm]
    congr 1; ext y
    congr 1; ext ξ
    ring
  rw [expand_rhs]
  simp_rw [key]
  simp only [mul_ite, mul_zero]
  simp_rw [Finset.sum_ite_eq' Finset.univ, Finset.mem_univ, if_true]
  have hcard : (card (Fin d → ZMod p) : ℂ) ≠ 0 := by
    rw [Fintype.card_pi_const, ZMod.card]
    exact_mod_cast pow_ne_zero d (Nat.Prime.ne_zero (Fact.out))
  rw [Finset.mul_sum]
  congr 1; ext x
  field_simp

end FourierFF


-- created on 2026-10-23
