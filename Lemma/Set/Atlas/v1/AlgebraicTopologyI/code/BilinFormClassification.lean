import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.BilinFormClassification
open BilinFormZMod2


/--
[BilinFormZMod2.case1_split](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/BilinFormClassification.lean)
-/
@[path]
lemma BilinFormZMod2.case1_split
  {V : Type u}
  [AddCommGroup V]
  [Module (ZMod 2) V]
  [Module.Finite (ZMod 2) V]
  {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V}
-- given
  (hB_symm : B.IsSymm)
  (hB_nondeg : B.Nondegenerate)
  (hv : v ≠ 0)
  (hvv : B v v ≠ 0)
  (ih : ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W], Module.finrank (ZMod 2) W < Module.finrank (ZMod 2) V → ∀ (B' : LinearMap.BilinForm (ZMod 2) W), B'.IsSymm → B'.Nondegenerate → ∃ (a b : ℕ) (e : W ≃ₗ[ZMod 2] (Fin a → ZMod 2) × (Fin b → Fin 2 → ZMod 2)), (LinearMap.BilinForm.congr e) B' = BilinFormZMod2.standardF2Form a b) :
-- imply
  ∃ (a b : ℕ) (e : V ≃ₗ[ZMod 2] (Fin a → ZMod 2) × (Fin b → Fin 2 → ZMod 2)), (LinearMap.BilinForm.congr e) B = BilinFormZMod2.standardF2Form a b := by
-- proof
  classical
  have hrefl : B.IsRefl := hB_symm.isRefl
  have hnotortho : ¬B.IsOrtho v v := hvv
  have hspan_nondeg : (B.restrict ((ZMod 2) ∙ v)).Nondegenerate :=
    B.nondegenerate_restrict_of_disjoint_orthogonal hrefl
      (disjoint_iff.mpr (LinearMap.BilinForm.span_singleton_inf_orthogonal_eq_bot hnotortho))
  have hortho_nondeg : (B.restrict (B.orthogonal ((ZMod 2) ∙ v))).Nondegenerate :=
    LinearMap.BilinForm.restrict_nondegenerate_orthogonal_spanSingleton B hB_nondeg hrefl hnotortho
  have hlt : Module.finrank (ZMod 2) ↥(B.orthogonal ((ZMod 2) ∙ v)) <
    Module.finrank (ZMod 2) V := by
    rw [LinearMap.BilinForm.finrank_orthogonal hB_nondeg, finrank_span_singleton hv]
    have : 0 < Module.finrank (ZMod 2) V := Module.finrank_pos_iff.mpr ⟨⟨v, ⟨0, hv⟩⟩⟩
    omega
  obtain ⟨a, b, e_ih, h_ih⟩ := ih _ hlt _ (hB_symm.restrict _) hortho_nondeg
  let e_split := BilinearForm.orthogonalProdEquiv B hrefl hspan_nondeg
  let e_span := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V v hv
  let e_rearr : (ZMod 2 × ((Fin a → ZMod 2) × (Fin b → Fin 2 → ZMod 2))) ≃ₗ[ZMod 2]
    ((Fin (a + 1) → ZMod 2) × (Fin b → Fin 2 → ZMod 2)) :=
    (LinearEquiv.prodAssoc (ZMod 2) (ZMod 2) (Fin a → ZMod 2) (Fin b → Fin 2 → ZMod 2)).symm ≪≫ₗ
      LinearEquiv.prodCongr (Fin.consLinearEquiv (ZMod 2) (fun _ => ZMod 2)) (LinearEquiv.refl _ _)
  let e_final : V ≃ₗ[ZMod 2] ((Fin (a + 1) → ZMod 2) × (Fin b → Fin 2 → ZMod 2)) :=
    (e_split.symm ≪≫ₗ LinearEquiv.prodCongr e_span.symm e_ih) ≪≫ₗ e_rearr
  refine ⟨a + 1, b, e_final, ?_⟩
  have hform_split := BilinearForm.orthogonalProdEquiv_respects_form B hrefl hspan_nondeg
  apply LinearMap.ext₂; intro x y
  simp only [LinearMap.BilinForm.congr_apply, BilinFormZMod2.standardF2Form, LinearMap.mk₂_apply]
  have he : ∀ z, e_final.symm z = e_split
    (e_span ((e_rearr.symm z).1), e_ih.symm ((e_rearr.symm z).2)) := fun _ => rfl
  rw [he, he, hform_split]
  have hBvv : B v v = 1 :=
    (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ hvv
  have hspan_form : ∀ (c d : ZMod 2),
    B (↑(e_span c) : V) (↑(e_span d) : V) = c * d := by
    intro c d
    show B ((LinearMap.toSpanSingleton (ZMod 2) V v) c)
      ((LinearMap.toSpanSingleton (ZMod 2) V v) d) = c * d
    simp only [LinearMap.toSpanSingleton_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      hBvv, mul_one, mul_comm]
  have hih_form : ∀ u w, B (↑(e_ih.symm u) : V) (↑(e_ih.symm w) : V) =
    BilinFormZMod2.standardF2Form a b u w := by
    intro u w
    have h : (LinearMap.BilinForm.congr e_ih (B.restrict (B.orthogonal ((ZMod 2) ∙ v)))) u w =
      BilinFormZMod2.standardF2Form a b u w := by rw [h_ih]
    simp only [LinearMap.BilinForm.congr_apply, LinearMap.BilinForm.restrict_apply] at h
    exact h
  rw [hspan_form, hih_form]
  simp only [e_rearr, LinearEquiv.symm_trans_apply, LinearEquiv.prodCongr_symm,
    LinearEquiv.refl_symm, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
    BilinFormZMod2.standardF2Form, LinearMap.mk₂_apply]
  simp only [Fin.consLinearEquiv, Fin.consEquiv, LinearEquiv.prodAssoc]
  dsimp [AddEquiv.prodAssoc, Equiv.prodAssoc, Fin.cons]
  simp only [Fin.tail]
  rw [Fin.sum_univ_succ]
  ring
noncomputable section
set_option autoImplicit false
namespace BilinFormZMod2
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace BilinFormZMod2

/--
[case2_split](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/BilinFormClassification.lean)
-/
@[path]
lemma case2_split
  {V : Type u}
  [AddCommGroup V]
  [Module (ZMod 2) V]
  [Module.Finite (ZMod 2) V]
  {B : LinearMap.BilinForm (ZMod 2) V}
-- given
  (hB_symm : B.IsSymm)
  (hB_nondeg : B.Nondegenerate)
  (hall : ∀ v : V, B v v = 0)
  (hV : Module.finrank (ZMod 2) V ≠ 0)
  (ih : ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W], Module.finrank (ZMod 2) W < Module.finrank (ZMod 2) V → ∀ (B' : LinearMap.BilinForm (ZMod 2) W), B'.IsSymm → B'.Nondegenerate → ∃ (a b : ℕ) (e : W ≃ₗ[ZMod 2] (Fin a → ZMod 2) × (Fin b → Fin 2 → ZMod 2)), (LinearMap.BilinForm.congr e) B' = standardF2Form a b) :
-- imply
  ∃ (a b : ℕ) (e : V ≃ₗ[ZMod 2] (Fin a → ZMod 2) × (Fin b → Fin 2 → ZMod 2)), (LinearMap.BilinForm.congr e) B = standardF2Form a b := by
-- proof
  classical
  have hrefl : B.IsRefl := hB_symm.isRefl
  have hV_pos : 0 < Module.finrank (ZMod 2) V := Nat.pos_of_ne_zero hV
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos hV_pos
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨w, hvw⟩ : ∃ w, B v w ≠ 0 := by
    by_contra h; push Not at h
    exact hv (hB_nondeg.1 v (fun w => h w))
  have hvw1 : B v w = 1 := (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ hvw
  have hw_ne : w ≠ 0 := by intro heq; simp [heq] at hvw
  have hlin : LinearIndependent (ZMod 2) ![v, w] := by
    rw [linearIndependent_fin2]
    exact ⟨hw_ne, fun a ha => by
      have haw : a • w = v := ha
      have hBvaw : B v (a • w) = a * (B v w) := by
        simp only [map_smul, smul_eq_mul]
      rw [haw, hall v, hvw1, mul_one] at hBvaw
      have ha0 : a = 0 := hBvaw.symm
      rw [ha0, zero_smul] at haw
      exact hv haw.symm⟩
  let Wspan := Submodule.span (ZMod 2) (Set.range ![v, w])
  have hWspan_finrank : Module.finrank (ZMod 2) Wspan = 2 := by
    rw [finrank_span_eq_card hlin, Fintype.card_fin]
  have hv_in : v ∈ Wspan := Submodule.subset_span ⟨0, rfl⟩
  have hw_in : w ∈ Wspan := Submodule.subset_span ⟨1, rfl⟩
  have hW_nondeg : (B.restrict Wspan).Nondegenerate := by
    rw [BilinearForm.restrict_nondegenerate_iff_disjoint_orthogonal B hrefl]
    rw [Submodule.disjoint_def]
    intro x hxW hxO
    have hBvx : B v x = 0 := hxO v hv_in
    have hBwx : B w x = 0 := hxO w hw_in
    have hBxv : B x v = 0 := by rw [hB_symm.eq x v]; exact hBvx
    have hBxw : B x w = 0 := by rw [hB_symm.eq x w]; exact hBwx
    rw [Submodule.mem_span_range_iff_exists_fun] at hxW
    obtain ⟨c, hc⟩ := hxW
    have hx_eq : x = c 0 • v + c 1 • w := by rw [← hc, Fin.sum_univ_two]; rfl
    have hBxv' : B x v = c 1 := by
      rw [hx_eq, map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.smul_apply, hall v, smul_zero, zero_add, smul_eq_mul,
        hB_symm.eq w v, hvw1, mul_one]
    have hBxw' : B x w = c 0 := by
      rw [hx_eq, map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.smul_apply, hvw1, smul_eq_mul, mul_one, hall w, smul_zero, add_zero]
    rw [hx_eq, hBxw'.symm.trans hBxw, hBxv'.symm.trans hBxv, zero_smul, zero_smul, zero_add]
  have hortho_nondeg : (B.restrict (B.orthogonal Wspan)).Nondegenerate :=
    BilinearForm.restrict_orthogonal_nondegenerate B hB_nondeg hrefl hW_nondeg
  have hlt : Module.finrank (ZMod 2) ↥(B.orthogonal Wspan) <
    Module.finrank (ZMod 2) V := by
    rw [LinearMap.BilinForm.finrank_orthogonal hB_nondeg, hWspan_finrank]; omega
  obtain ⟨a, b, e_ih, h_ih⟩ := ih _ hlt _ (hB_symm.restrict _) hortho_nondeg
  let e_split := BilinearForm.orthogonalProdEquiv B hrefl hW_nondeg
  let basisVW := Module.Basis.span hlin
  let e_basis : Wspan ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) := basisVW.equivFun
  let e_rearr := finSuccEquiv a b
  let e_final : V ≃ₗ[ZMod 2] ((Fin a → ZMod 2) × (Fin (b + 1) → Fin 2 → ZMod 2)) :=
    (e_split.symm ≪≫ₗ LinearEquiv.prodCongr e_basis e_ih) ≪≫ₗ e_rearr
  refine ⟨a, b + 1, e_final, ?_⟩
  have hform_split := BilinearForm.orthogonalProdEquiv_respects_form B hrefl hW_nondeg
  apply LinearMap.ext₂; intro x y
  simp only [LinearMap.BilinForm.congr_apply, standardF2Form, LinearMap.mk₂_apply]
  have he : ∀ z, e_final.symm z = e_split
    (e_basis.symm ((e_rearr.symm z).1), e_ih.symm ((e_rearr.symm z).2)) := fun _ => rfl
  rw [he, he, hform_split]
  have hspan_form : ∀ (p q : Fin 2 → ZMod 2),
    B (↑(e_basis.symm p) : V) (↑(e_basis.symm q) : V) =
    p 0 * q 1 + p 1 * q 0 := by
    intro p q
    have he_expand : ∀ r : Fin 2 → ZMod 2,
      (e_basis.symm r : V) = r 0 • v + r 1 • w := by
      intro r
      have hb0 : (basisVW 0 : V) = v := Module.Basis.coe_span_apply hlin 0
      have hb1 : (basisVW 1 : V) = w := Module.Basis.coe_span_apply hlin 1
      change (↑(basisVW.equivFun.symm r) : V) = r 0 • v + r 1 • w
      simp only [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two]
      simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, hb0, hb1]
    rw [he_expand, he_expand]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hall v, hall w, hvw1, hB_symm.eq w v, hvw1]
    ring
  have hih_form : ∀ u₁ u₂, B (↑(e_ih.symm u₁) : V) (↑(e_ih.symm u₂) : V) =
    standardF2Form a b u₁ u₂ := by
    intro u₁ u₂
    have h : (LinearMap.BilinForm.congr e_ih (B.restrict (B.orthogonal Wspan))) u₁ u₂ =
      standardF2Form a b u₁ u₂ := by rw [h_ih]
    simp only [LinearMap.BilinForm.congr_apply, LinearMap.BilinForm.restrict_apply] at h
    exact h
  rw [hspan_form, hih_form]
  simp only [e_rearr, finSuccEquiv, standardF2Form, LinearMap.mk₂_apply]
  simp only [LinearEquiv.coe_symm_mk]
  rw [Fin.sum_univ_succ]
  ring

end BilinFormZMod2

namespace BilinFormZMod2

/--
[exists_isometry_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/BilinFormClassification.lean)
-/
@[path]
lemma exists_isometry_aux
  {n : ℕ} :
-- imply
  ∀ (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V], Module.finrank (ZMod 2) V = n → ∀ (B : LinearMap.BilinForm (ZMod 2) V), B.IsSymm → B.Nondegenerate → ∃ (a b : ℕ) (e : V ≃ₗ[ZMod 2] (Fin a → ZMod 2) × (Fin b → Fin 2 → ZMod 2)), (LinearMap.BilinForm.congr e) B = standardF2Form a b := by
-- proof
  induction n using Nat.strongRecOn with
  | _ n ih_ind =>
    intro V _ _ _ hn B hB_symm hB_nondeg
    by_cases hn0 : n = 0
    ·
      subst hn0
      haveI : Subsingleton V := by
        rwa [Module.finrank_eq_zero_iff_of_free] at hn
      exact ⟨0, 0, LinearEquiv.ofSubsingleton V _, Subsingleton.elim _ _⟩
    ·
      by_cases hcase : ∃ v : V, B v v ≠ 0
      ·
        obtain ⟨v, hvv⟩ := hcase
        have hv : v ≠ 0 := by
          intro heq
          exact absurd (by subst heq; simp only [map_zero]) hvv
        exact case1_split B hB_symm hB_nondeg v hv hvv
          (fun W _ _ _ hlt BW hBW_symm hBW_nondeg =>
            ih_ind (Module.finrank (ZMod 2) W) (hn ▸ hlt) W rfl BW hBW_symm hBW_nondeg)
      ·
        push Not at hcase
        exact case2_split B hB_symm hB_nondeg hcase (hn ▸ hn0)
          (fun W _ _ _ hlt BW hBW_symm hBW_nondeg =>
            ih_ind (Module.finrank (ZMod 2) W) (hn ▸ hlt) W rfl BW hBW_symm hBW_nondeg)

end BilinFormZMod2

namespace BilinFormZMod2

/--
[exists_isometry_standardF2Form](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/BilinFormClassification.lean)
-/
@[path]
lemma exists_isometry_standardF2Form
  [AddCommGroup V]
  [Module (ZMod 2) V]
  [Module.Finite (ZMod 2) V]
  {B : LinearMap.BilinForm (ZMod 2) V}
-- given
  (hB_symm : B.IsSymm)
  (hB_nondeg : B.Nondegenerate) :
-- imply
  ∃ (a b : ℕ) (e : V ≃ₗ[ZMod 2] (Fin a → ZMod 2) × (Fin b → Fin 2 → ZMod 2)), (LinearMap.BilinForm.congr e) B = standardF2Form a b :=
-- proof
  exists_isometry_aux _ V rfl B hB_symm hB_nondeg
end BilinFormZMod2
end



-- created on 2026-10-23
