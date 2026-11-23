module

public import Mathlib
public import Theorem.Scheme.OrderedAffineCoverCech
public import Def.AlgebraicGeometry_OrderedAffineCoverOf
public import Instance.AlgebraicGeometry_OModulePresheafLerayBicomplex
public import Abbrev.AlgebraicGeometry_OModulePresheafLerayBicomplex

public noncomputable section

set_option autoImplicit false

noncomputable section

namespace AlgebraicGeometry.OModulePresheaf.Leray

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Scheme

section FiberAffine

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}

public theorem _root_.AlgebraicGeometry.Scheme.OrderedAffineCover.fiberAffineOpen
    (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R)) [IsSeparated πZ]
    {W : V'.Opens} (hW : IsAffineOpen W) {U : Z.Opens} (hU : IsAffineOpen U) :
    IsAffineOpen (W ⊓ (Opens.map p.base).obj U) := by
  have hpb₁ := isPullback_opens_inf W ((Opens.map p.base).obj U)
  have hpb₂ := isPullback_morphismRestrict p U
  have hpb : IsPullback (V'.homOfLE (inf_le_left : W ⊓ (Opens.map p.base).obj U ≤ W))
      (V'.homOfLE inf_le_right ≫ (p ∣_ U)) (W.ι ≫ p) U.ι :=
    (hpb₁.flip.paste_horiz hpb₂).flip
  haveI : IsAffine (W : Scheme.{u}) := hW
  haveI : IsAffine (U : Scheme.{u}) := hU
  haveI haffSR : IsAffine (pullback ((W.ι ≫ p) ≫ πZ) (U.ι ≫ πZ)) := inferInstance
  haveI hcl : IsClosedImmersion (pullback.mapDesc (W.ι ≫ p) U.ι πZ) := inferInstance
  haveI : IsAffine (pullback (W.ι ≫ p) U.ι) :=
    isAffine_of_isAffineHom (pullback.mapDesc (W.ι ≫ p) U.ι πZ)
  exact .of_isIso hpb.isoPullback.hom


@[simp] public theorem restrictToPreimage_U
    (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R)) [IsSeparated πZ]
    (K' : Scheme.OrderedAffineCover V') {U : Z.Opens} (hU : IsAffineOpen U) (i : K'.ι) :
    (restrictToPreimage p πZ K' hU).U i = K'.U i ⊓ (Opens.map p.base).obj U := rfl

end FiberAffine

section LerayDC

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R))
variable (K : Scheme.OrderedAffineCover Z) (K' : Scheme.OrderedAffineCover V')


public theorem dH_apply (a b : ℕ) (f : biC p πZ K K' a b)
    (στ : BiIdx K K' (a + 1) b) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    dH p πZ K K' a b f στ
      = ∑ j : Fin (a + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          Scheme.OrderedAffineCoverOf.res (p ≫ πZ)
            (inf_le_inf_left _ ((Opens.map p.base).monotone
              (K.inter_le_inter_face στ.1 j)))
            (f ⟨K.face στ.1 j, στ.2⟩) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  simp only [dH, LinearMap.pi_apply, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => rfl


public theorem dH_apply' (a b : ℕ) (f : biC p πZ K K' a b)
    (στ : BiIdx K K' (a + 1) b) :
    dH p πZ K K' a b f στ
      = ∑ j : Fin (a + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          (V'.presheaf.map (homOfLE (inf_le_inf_left (K'.inter στ.2)
            ((Opens.map p.base).monotone (K.inter_le_inter_face στ.1 j)))).op).hom
            (f ⟨K.face στ.1 j, στ.2⟩) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  simp only [dH, LinearMap.pi_apply, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => rfl


public theorem dV_apply (a b : ℕ) (f : biC p πZ K K' a b)
    (στ : BiIdx K K' a (b + 1)) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    dV p πZ K K' a b f στ
      = ∑ j : Fin (b + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          Scheme.OrderedAffineCoverOf.res (p ≫ πZ)
            (inf_le_inf_right _ (K'.inter_le_inter_face στ.2 j))
            (f ⟨στ.1, K'.face στ.2 j⟩) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  simp only [dV, LinearMap.pi_apply, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => rfl


public theorem dV_apply' (a b : ℕ) (f : biC p πZ K K' a b)
    (στ : BiIdx K K' a (b + 1)) :
    dV p πZ K K' a b f στ
      = ∑ j : Fin (b + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          (V'.presheaf.map (homOfLE (inf_le_inf_right
            ((Opens.map p.base).obj (K.inter στ.1))
            (K'.inter_le_inter_face στ.2 j))).op).hom
            (f ⟨στ.1, K'.face στ.2 j⟩) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  simp only [dV, LinearMap.pi_apply, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => rfl


public theorem biC_subsingleton (a b : ℕ)
    (h : max (Fintype.card K.ι) (Fintype.card K'.ι) ≤ a
          ∨ max (Fintype.card K.ι) (Fintype.card K'.ι) ≤ b) :
    Subsingleton (biC p πZ K K' a b) := by
  have hempty : IsEmpty (BiIdx K K' a b) := by
    rcases h with ha | hb
    · exact ⟨fun στ => absurd
        (Fintype.card_fin (a + 1) ▸ Fintype.card_le_of_injective στ.1.1 στ.1.2.injective)
        (by omega)⟩
    · exact ⟨fun στ => absurd
        (Fintype.card_fin (b + 1) ▸ Fintype.card_le_of_injective στ.2.1 στ.2.2.injective)
        (by omega)⟩
  exact ⟨fun f g => funext fun στ => (hempty.false στ).elim⟩

end LerayDC

section RelAlt

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R))
variable (K' : Scheme.OrderedAffineCover V')


public theorem relAltd_apply' (U : Z.Opens) (b : ℕ)
    (f : relAltC p πZ K' U b) (τ : K'.Idx (b + 1)) :
    relAltd p πZ K' U b f τ
      = ∑ j : Fin (b + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          (V'.presheaf.map (homOfLE (inf_le_inf_right ((Opens.map p.base).obj U)
            (K'.inter_le_inter_face τ j))).op).hom
            (f (K'.face τ j)) := by
  simp only [relAltd, LinearMap.pi_apply, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => rfl


public theorem relAltd_eq_d (U : Z.Opens) (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    relAltd p πZ K' U b
      = OModulePresheaf.d (pushOpen p πZ U) K' b := rfl


public theorem relAltd_Γsmul (U : Z.Opens) (b : ℕ) (a : Γ(Z, U))
    (f : relAltC p πZ K' U b) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    relAltd p πZ K' U b (a • f) = a • relAltd p πZ K' U b f := by

  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  have hstep : ∀ (W₁ W₂ : V'.Opens) (h : W₁ ≤ W₂)
      (e₁ : W₁ ⊓ (Opens.map p.base).obj U ≤ p ⁻¹ᵁ U)
      (e₂ : W₂ ⊓ (Opens.map p.base).obj U ≤ p ⁻¹ᵁ U)
      (x : Γ(V', W₂ ⊓ (Opens.map p.base).obj U)),
      (V'.presheaf.map (homOfLE (inf_le_inf_right ((Opens.map p.base).obj U) h)).op).hom
          ((p.appLE U (W₂ ⊓ (Opens.map p.base).obj U) e₂).hom a * x)
        = (p.appLE U (W₁ ⊓ (Opens.map p.base).obj U) e₁).hom a
          * (V'.presheaf.map (homOfLE (inf_le_inf_right ((Opens.map p.base).obj U) h)).op).hom x :=
    fun _ _ _ _ _ _ => by rw [map_mul, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  funext τ
  refine (relAltd_apply' p πZ K' U b (a • f) τ).trans
    ((Finset.sum_congr rfl fun (j : Fin (b + 2)) _ =>
      (congrArg (((-1 : ℤ) ^ (j : ℕ)) • ·)
        (hstep (K'.inter τ) (K'.inter (K'.face τ j))
          (K'.inter_le_inter_face τ j) inf_le_right inf_le_right
          (f (K'.face τ j)))).trans (mul_smul_comm _ _ _).symm).trans ?_)
  rw [← Finset.mul_sum, ← relAltd_apply' p πZ K' U b f τ]
  rfl


public theorem relAltHB_Γsmul (U : Z.Opens) (b : ℕ) (a : Γ(Z, U))
    (x : letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
      ↥(LinearMap.ker (relAltd p πZ K' U b)))
    (hx : x ∈ relAltHB p πZ K' U b) :
    a • x ∈ relAltHB p πZ K' U b := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  rcases b with _ | b'
  · exact (Submodule.mem_bot R).mpr (by rw [(Submodule.mem_bot R).mp hx, smul_zero])
  · obtain ⟨y, hy⟩ := hx
    exact ⟨a • y, (relAltd_Γsmul p πZ K' U b' a y).trans
      (congrArg (a • ·) hy)⟩


public theorem relRes_apply {U U' : Z.Opens} (h : U ≤ U') (b : ℕ) (f : relAltC p πZ K' U' b) (τ : K'.Idx b) :
    relRes p πZ K' h b f τ
      = (V'.presheaf.map (homOfLE (inf_le_inf_left (K'.inter τ) ((Opens.map p.base).monotone h))).op).hom
          (f τ) := rfl


public theorem relRes_comm {U U' : Z.Opens} (h : U ≤ U') (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    relRes p πZ K' h (b + 1) ∘ₗ relAltd p πZ K' U' b = relAltd p πZ K' U b ∘ₗ relRes p πZ K' h b := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  refine LinearMap.ext fun f => funext fun τ => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, relRes_apply, relAltd_apply', relAltd_apply', map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, relRes_apply]
  congr 1
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
  rfl


public theorem relResKer_coe {U U' : Z.Opens} (h : U ≤ U') (b : ℕ)
    (x : letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ); ↥(LinearMap.ker (relAltd p πZ K' U' b))) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    (relResKer p πZ K' h b x : relAltC p πZ K' U b) = relRes p πZ K' h b x := rfl


public theorem relAltHB_res_le {U U' : Z.Opens} (h : U ≤ U') (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    relAltHB p πZ K' U' b
      ≤ (relAltHB p πZ K' U b).comap
          (relResKer p πZ K' h b) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  rcases b with _ | b'
  · exact bot_le
  · rintro x ⟨y, hy⟩
    exact ⟨relRes p πZ K' h b' y,
      (LinearMap.congr_fun (relRes_comm p πZ K' h b') y).symm.trans
        (congrArg (relRes p πZ K' h (b' + 1)) hy)⟩


public theorem dV_uncurry (a b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    ∀ x σ, biC_uncurry p πZ K K' a (b + 1)
        (dV p πZ K K' a b x) σ
      = relAltd p πZ K' (K.inter σ) b
          (biC_uncurry p πZ K K' a b x σ) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  intro x σ; funext τ
  simp only [biC_uncurry, dV, relAltd,
    LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.pi_apply,
    LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun d _ => rfl


public theorem dH_uncurry (a b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    ∀ x τ, biC_uncurry' p πZ K K' (a + 1) b
        (dH p πZ K K' a b x) τ
      = OModulePresheaf.d (pullOpen p πZ (K'.inter τ))
          K a (biC_uncurry' p πZ K K' a b x τ) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  intro x τ; funext σ
  simp only [biC_uncurry', dH, OModulePresheaf.d,
    LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.pi_apply,
    LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun d _ => rfl

end E2Iso

end AlgebraicGeometry.OModulePresheaf.Leray

end
