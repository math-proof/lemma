import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

variable {X : (Scheme : Type 1)}
private lemma res_res {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : (X.presheaf.obj (op U))) :
  X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op s) = X.presheaf.map (homOfLE (h₂.trans h₁)).op s := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  rfl
private lemma res_gen {U V W : X.Opens} (i : V ⟶ U) (j : W ⟶ V) (s : (X.presheaf.obj (op U))) :
  X.presheaf.map j.op (X.presheaf.map i.op s) = X.presheaf.map (j ≫ i).op s := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  rfl
/--
[AlgebraicGeometry_Scheme_exists_isUnit_mul_pow_eq_mul_pow_of_isDiscreteValuationRing_stalk](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_isUnit_mul_pow_eq_mul_pow_of_isDiscreteValuationRing_stalk.lean)
-/
@[path]
private lemma main
  {X : (Scheme : Type 1)} (t : (X.presheaf.obj (op ⊤))) (ξ : X)
    [IsDomain (X.presheaf.stalk ξ)] [IsDiscreteValuationRing (X.presheaf.stalk ξ)]
    (hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) = Ideal.span {X.presheaf.Γgerm ξ t})
    (W : X.Opens) (hξ : ξ ∈ W) (u : (X.presheaf.obj (op (W ⊓ X.basicOpen t)))) (hu : IsUnit u) :
    ∃ (W' : X.Opens) (hW' : W' ≤ W) (_ : ξ ∈ W') (a b : ℕ) (v : (X.presheaf.obj (op W'))), IsUnit v ∧
      X.presheaf.map (homOfLE (inf_le_inf_right (X.basicOpen t) hW')).op u *
          X.presheaf.map (homOfLE (le_top (a := W' ⊓ X.basicOpen t))).op t ^ a =
        X.presheaf.map (homOfLE (inf_le_left (a := W') (b := X.basicOpen t))).op v *
          X.presheaf.map (homOfLE (le_top (a := W' ⊓ X.basicOpen t))).op t ^ b := by
  classical
  obtain ⟨_, ⟨W₁, hW₁aff, rfl⟩, hξW₁, hW₁W⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hξ W.isOpen
  set tW : (X.presheaf.obj (op W₁)) := X.presheaf.map (homOfLE (le_top (a := W₁))).op t with htW
  have hbo : X.basicOpen tW = W₁ ⊓ X.basicOpen t := by
    rw [htW]
    apply X.basicOpen_res t (homOfLE (le_top (a := W₁))).op
  let _ : IsLocalization.Away tW (X.presheaf.obj (op (X.basicOpen tW))) := hW₁aff.isLocalization_basicOpen tW
  have hle : X.basicOpen tW ≤ W ⊓ X.basicOpen t := by
    rw [hbo]
    apply inf_le_inf_right _ hW₁W
  set u₁ : (X.presheaf.obj (op (X.basicOpen tW))) := X.presheaf.map (homOfLE hle).op u with hu₁
  have hu₁u : IsUnit u₁ := hu.map _
  obtain ⟨a, c, hca⟩ := IsLocalization.Away.surj tW u₁
  obtain ⟨a', c', hca'⟩ := IsLocalization.Away.surj tW (↑(hu₁u.unit⁻¹) : (X.presheaf.obj (op (X.basicOpen tW))))
  have hcc' : algebraMap (X.presheaf.obj (op W₁)) (X.presheaf.obj (op (X.basicOpen tW))) (c * c') =
      algebraMap (X.presheaf.obj (op W₁)) (X.presheaf.obj (op (X.basicOpen tW))) (tW ^ (a + a')) := by
    rw [map_mul, ← hca, ← hca', map_pow, pow_add]
    have : u₁ * (↑(hu₁u.unit⁻¹) : (X.presheaf.obj (op (X.basicOpen tW)))) = 1 := hu₁u.mul_val_inv
    calc
      _ = (u₁ * ↑(hu₁u.unit⁻¹)) * (algebraMap _ _ tW ^ a * algebraMap _ _ tW ^ a') := by ring
      _ = algebraMap _ _ tW ^ a * algebraMap _ _ tW ^ a' := by rw [this, one_mul]
  obtain ⟨⟨_, ⟨N, rfl⟩⟩, hN⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers tW) _).mp hcc'
  let γ := X.presheaf.germ W₁ ξ hξW₁
  set ϖ := X.presheaf.Γgerm ξ t with hϖ
  have hγt : γ tW = ϖ := by
    rw [htW, hϖ]
    apply TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top (a := W₁))) ξ hξW₁ t
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field (X.presheaf.stalk ξ)
    rw [hmax, h0, Ideal.span_singleton_eq_bot]
  have hirr : Irreducible ϖ := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal ϖ hϖ0 hmax
  have hγcc' : γ c * γ c' = ϖ ^ (a + a') := by
    have h1 := congrArg γ hN
    simp only [map_mul, map_pow, hγt] at h1
    apply mul_left_cancel₀ (pow_ne_zero N hϖ0) h1
  have hγc : γ c ≠ 0 := by
    intro h0
    apply pow_ne_zero (a + a') hϖ0
    rw [← hγcc', h0, zero_mul]
  obtain ⟨b, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hγc hirr
  obtain ⟨Uw, hξUw, sw, hsw⟩ := TopCat.Presheaf.exists_germ_eq (x := ξ) X.presheaf (↑w)
  have hwu : IsUnit (X.presheaf.germ Uw ξ hξUw sw) := by
    rw [hsw]
    apply Units.isUnit w
  obtain ⟨Uw', iw, hξUw', hswu⟩ := RingedSpace.isUnit_res_of_isUnit_germ X.toLocallyRingedSpace.toRingedSpace Uw sw ξ hξUw hwu
  have hgerm : X.presheaf.germ W₁ ξ hξW₁ c =
      X.presheaf.germ (W₁ ⊓ Uw') ξ ⟨hξW₁, hξUw'⟩
        (X.presheaf.map (homOfLE inf_le_right).op (X.presheaf.map iw.op sw) *
          X.presheaf.map (homOfLE inf_le_left).op tW ^ b) := by
    rw [map_mul, map_pow, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
      TopCat.Presheaf.germ_res_apply]
    change γ c = _ * γ tW ^ b
    rw [hw, hγt]
    congr 1
    apply hsw.symm
  obtain ⟨W₂, hξW₂, i₁, i₂, heq⟩ := TopCat.Presheaf.germ_eq (U := W₁) (V := W₁ ⊓ Uw') X.presheaf ξ hξW₁ ⟨hξW₁, hξUw'⟩ _ _ hgerm
  have hW₂W₁ : W₂ ≤ W₁ := i₁.le
  have hW₂W : W₂ ≤ W := fun x hx => hW₁W (hW₂W₁ hx)
  refine ⟨W₂, hW₂W, hξW₂, a, b,
    X.presheaf.map (homOfLE (i₂.le.trans inf_le_right)).op (X.presheaf.map iw.op sw), ?_, ?_⟩
  · apply hswu.map _
  ·
    have hsub : W₂ ⊓ X.basicOpen t ≤ X.basicOpen tW := by
      rw [hbo]
      apply inf_le_inf_right _ hW₂W₁
    have h1 := congrArg (X.presheaf.map (homOfLE hsub).op) hca
    rw [map_mul, map_pow] at h1
    have e1 : X.presheaf.map (homOfLE hsub).op u₁ =
        X.presheaf.map (homOfLE (inf_le_inf_right (X.basicOpen t) hW₂W)).op u := by
      rw [hu₁, res_res]
    have e2 : X.presheaf.map (homOfLE hsub).op (algebraMap (X.presheaf.obj (op W₁)) (X.presheaf.obj (op (X.basicOpen tW))) tW) =
        X.presheaf.map (homOfLE (le_top (a := W₂ ⊓ X.basicOpen t))).op t := by
      show X.presheaf.map (homOfLE hsub).op (X.presheaf.map (homOfLE (X.basicOpen_le tW)).op
        (X.presheaf.map (homOfLE (le_top (a := W₁))).op t)) = _
      rw [res_res, res_res]
    have e3 : X.presheaf.map (homOfLE hsub).op (algebraMap (X.presheaf.obj (op W₁)) (X.presheaf.obj (op (X.basicOpen tW))) c) =
        X.presheaf.map (homOfLE (inf_le_left (a := W₂) (b := X.basicOpen t))).op (X.presheaf.map i₁.op c) := by
      show X.presheaf.map (homOfLE hsub).op (X.presheaf.map (homOfLE (X.basicOpen_le tW)).op c) = _
      rw [res_res, res_gen]
      rfl
    simp only [map_mul, map_pow, res_gen] at heq
    have e4 : X.presheaf.map (i₂ ≫ homOfLE (inf_le_left : W₁ ⊓ Uw' ≤ W₁)).op tW =
        X.presheaf.map (homOfLE (le_top (a := W₂))).op t := by
      show X.presheaf.map _ (X.presheaf.map _ t) = _
      rw [res_gen]
      rfl
    rw [e4] at heq
    rw [e1, e2, e3, heq] at h1
    simp only [map_mul, map_pow, res_gen] at h1 ⊢
    apply h1


-- created on 2026-10-20
