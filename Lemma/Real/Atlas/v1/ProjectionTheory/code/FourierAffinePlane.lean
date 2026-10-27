import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProjectionTheory.code.FourierAffinePlane
open Finset hiding card Fintype (card) FourierFF
open Fintype (card)
open scoped BigOperators Classical


namespace FourierFF

/--
[norm_dft_cosetIndicator](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FourierAffinePlane.lean)
-/
@[path]
lemma norm_dft_cosetIndicator
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {d : ℕ}
  {e : AddChar (ZMod p) ℂ}
  {V : Submodule (ZMod p) (Fin d → ZMod p)}
  {a ξ : Fin d → ZMod p}
-- given
  (he : e ≠ 0) :
-- imply
  ‖dft e (cosetIndicator V a) ξ‖ = if ξ ∈ dotProdAnnihilator V then (card V : ℝ) else 0 := by
-- proof
  have hdft : dft e (cosetIndicator V a) ξ =
    e (-(dotProd ξ a)) * ∑ v : V, e (-(dotProd ξ (↑v : Fin d → ZMod p))) := by
    simp only [dft, cosetIndicator, fourierChar, AddChar.compAddMonoidHom_apply,
      dotProd, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddChar.inv_apply, boole_mul]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have hfilt : Finset.univ.filter (fun x => x - a ∈ V) =
      Finset.univ.image (fun v : V => (↑v : Fin d → ZMod p) + a) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Subtype.exists]
      exact ⟨fun hx => ⟨x - a, hx, sub_add_cancel x a⟩,
        fun ⟨v, hv, h⟩ => by rw [← h]; simpa using hv⟩
    rw [hfilt, Finset.sum_image (fun v1 _ v2 _ h => Subtype.ext (add_right_cancel h))]
    rw [Finset.mul_sum]
    congr 1; ext v
    rw [← AddChar.map_add_eq_mul]
    congr 1
    simp [add_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [hdft, norm_mul, AddChar.norm_apply, one_mul]
  set ψ : AddChar V ℂ :=
    (e.compAddMonoidHom (dotProd (-ξ))).compAddMonoidHom V.subtype.toAddMonoidHom
  have hsum_eq : ∑ v : V, e (-(dotProd ξ (↑v : Fin d → ZMod p))) = ∑ v : V, ψ v := by
    congr 1; ext ⟨v, hv⟩
    simp [ψ, AddChar.compAddMonoidHom_apply, dotProd, mul_neg, Finset.sum_neg_distrib]
  rw [hsum_eq]
  by_cases hann : ξ ∈ dotProdAnnihilator V
  ·
    rw [if_pos hann]
    have htriv : ψ = 0 := by
      rw [show (0 : AddChar V ℂ) = 1 from by ext; simp]
      ext ⟨v, hv⟩
      simp only [ψ, AddChar.compAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe,
        Submodule.subtype_apply, AddChar.one_apply]
      have hdp : dotProd (-ξ) v = 0 := by
        simp [dotProd, mul_neg, Finset.sum_neg_distrib, neg_eq_zero]
        exact hann v hv
      rw [hdp]; exact AddChar.map_zero_eq_one e
    simp [htriv, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ·
    rw [if_neg hann]
    have hne : ψ ≠ 0 := by
      rw [show (0 : AddChar V ℂ) = 1 from by ext; simp]
      intro h; apply hann
      intro v hv
      have := DFunLike.ext_iff.mp h ⟨v, hv⟩
      simp only [ψ, AddChar.compAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe,
        Submodule.subtype_apply, AddChar.one_apply] at this
      have h01 : (0 : AddChar (ZMod p) ℂ) = 1 := by ext x; simp
      have he1 : e ≠ 1 := by rwa [← h01]
      have hprim := AddChar.IsPrimitive.of_ne_one he1
      have hdp : dotProd (-ξ) v = 0 := (hprim.zmod_char_eq_one_iff p _).mp this
      simp [dotProd, mul_neg, Finset.sum_neg_distrib, neg_eq_zero] at hdp
      exact hdp
    rw [AddChar.sum_eq_zero_iff_ne_zero.mpr hne, norm_zero]

end FourierFF


-- created on 2026-10-23
