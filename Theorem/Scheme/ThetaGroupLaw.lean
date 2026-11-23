module

public import Theorem.Scheme.ThetaGroupAction
public import Theorem.Scheme.ThetaGroup
public import Instance.AlgebraicGeometry_ThetaGroupLaw

public noncomputable section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian Scheme
  TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules.fibration

public theorem mapComp_inv_app {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z) (M : Z.Modules) :
    (fibration.mapComp b.op.toLoc a.op.toLoc).inv.toNatTrans.app M = (pullbackComp a b).hom.app M := by
  simp [fibration, Pseudofunctor.comp_mapComp]
  exact Category.id_comp _


public theorem mapId_inv_app (X : Scheme.{0}) (N : X.Modules) :
    (fibration.mapId ⟨Opposite.op X⟩).inv.toNatTrans.app N = (pullbackId X).inv.app N := by
  simp [fibration, Pseudofunctor.comp_mapId]
  exact Category.id_comp _


public theorem pullbackCongr_hom_app_eq_eqToHom {X Y : Scheme.{0}} {a b : X ⟶ Y} (h : a = b) (M : Y.Modules) :
    (pullbackCongr h).hom.app M = eqToHom (by rw [h]) := by
  subst h; simp [pullbackCongr]


public theorem pullbackCongr_inv_app_eq_eqToHom {X Y : Scheme.{0}} {a b : X ⟶ Y} (h : a = b) (M : Y.Modules) :
    (pullbackCongr h).inv.app M = eqToHom (by rw [h]) := by
  subst h; simp [pullbackCongr]

variable {X : Scheme.{0}} (M : X.Modules)


@[simp] public theorem autOfIso_hom_base (e : X ≅ X) (φ : (Scheme.Modules.pullback e.hom).obj M ≅ M) :
    (autOfIso M e φ).hom.base = e.hom := rfl

@[simp] public theorem autOfIso_hom_fiber (e : X ≅ X) (φ : (Scheme.Modules.pullback e.hom).obj M ≅ M) :
    (autOfIso M e φ).hom.fiber = φ.inv := rfl


public theorem autOfIso_trans (e₁ e₂ e₁₂ : X ≅ X) (h : e₁₂.hom = e₁.hom ≫ e₂.hom)
    (φ₁ : (Scheme.Modules.pullback e₁.hom).obj M ≅ M) (φ₂ : (Scheme.Modules.pullback e₂.hom).obj M ≅ M) :
    autOfIso M e₁₂ (transIso M e₁ e₂ e₁₂ h φ₁ φ₂) = autOfIso M e₁ φ₁ ≪≫ autOfIso M e₂ φ₂ := by
  apply Iso.ext
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ h ?_
  simp only [Iso.trans_hom, Pseudofunctor.CoGrothendieck.categoryStruct_comp_fiber, autOfIso_hom_fiber,
    autOfIso_hom_base, RiemannForm.modulePair_fiber, fibration_map_toFunctor, mapComp_inv_app]
  simp only [transIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_inv, Iso.app_hom, Category.assoc,
    pullbackCongr_inv_app_eq_eqToHom]
  rfl


public theorem autOfIso_refl (e : X ≅ X) (h : e.hom = 𝟙 X) : autOfIso M e (reflIso M e h) = Iso.refl _ := by
  apply Iso.ext
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ h ?_
  simp only [Iso.refl_hom, Pseudofunctor.CoGrothendieck.categoryStruct_id_fiber, autOfIso_hom_fiber,
    RiemannForm.modulePair_fiber, RiemannForm.modulePair_base, mapId_inv_app]
  simp only [reflIso, Iso.trans_inv, Iso.app_inv, pullbackCongr_inv_app_eq_eqToHom]
  rfl


public theorem transIso_symmIso (e e' : X ≅ X) (h : e'.hom ≫ e.hom = 𝟙 X) (φ : (Scheme.Modules.pullback e.hom).obj M ≅ M) :
    transIso M e' e (Iso.refl X) h.symm (symmIso M e e' h φ) φ = reflIso M (Iso.refl X) rfl := by
  ext : 1
  simp [transIso, symmIso, reflIso, pullbackCongr_hom_app_eq_eqToHom]


public theorem autOfIso_symm_trans (e e' : X ≅ X) (h : e'.hom ≫ e.hom = 𝟙 X) (φ : (Scheme.Modules.pullback e.hom).obj M ≅ M) :
    autOfIso M e' (symmIso M e e' h φ) ≪≫ autOfIso M e φ = Iso.refl _ := by
  rw [← autOfIso_trans M e' e (Iso.refl X) h.symm (symmIso M e e' h φ) φ, transIso_symmIso, autOfIso_refl]


public theorem autOfIso_injective (e : X ≅ X) (φ φ' : (Scheme.Modules.pullback e.hom).obj M ≅ M)
    (h : autOfIso M e φ = autOfIso M e φ') : φ = φ' := by
  have h1 := Pseudofunctor.CoGrothendieck.Hom.congr (congrArg Iso.hom h)
  simp only [autOfIso_hom_fiber, autOfIso_hom_base, eqToHom_refl, Category.comp_id] at h1
  have h2 : φ.symm = φ'.symm := Iso.ext h1
  simpa using congrArg Iso.symm h2

end AlgebraicGeometry.Scheme.Modules.fibration

namespace AlgebraicGeometry.Scheme.Modules

section Homothety

variable {Y : Scheme.{0}} (N : Y.Modules)


public theorem map_topRes (r : Γ(Y, ⊤)) {U V : Y.Opens} (i : V ⟶ U) :
    Y.presheaf.map i.op (topRes r U) = topRes r V := by
  change (Y.presheaf.map _ ≫ Y.presheaf.map i.op) r = _
  rw [← Functor.map_comp]
  rfl


public theorem topRes_top (r : Γ(Y, ⊤)) : topRes r ⊤ = r := by
  change Y.presheaf.map _ r = r
  have : (homOfLE (le_top (a := (⊤ : Y.Opens)))).op = 𝟙 _ := rfl
  rw [this, Y.presheaf.map_id]; rfl


public theorem topRes_one (U : Y.Opens) : topRes (1 : Γ(Y, ⊤)) U = 1 := map_one _

public theorem topRes_mul (r r' : Γ(Y, ⊤)) (U : Y.Opens) : topRes (r * r') U = topRes r U * topRes r' U := map_mul _ _ _


@[simp] public theorem homothety_app (r : Γ(Y, ⊤)) (U : Y.Opens) (s : Γ(N, U)) :
    (homothety N r).app U s = topRes r U • s := rfl


public theorem homothety_one : homothety N 1 = 𝟙 N := by
  ext U s
  rw [homothety_app, topRes_one, one_smul, Scheme.Modules.Hom.id_app]; rfl


public theorem homothety_mul (r r' : Γ(Y, ⊤)) : homothety N (r * r') = homothety N r' ≫ homothety N r := by
  ext U s
  rw [homothety_app, topRes_mul, mul_smul, Scheme.Modules.Hom.comp_app]; rfl


public theorem constPtR_coe (x : SchemeHomOver t f) : (constPtR f t x).1 = pullback.snd f t ≫ x.1 := rfl


public theorem translate_fst (x : SchemeHomOver t f) :
    translate f L t x ≫ pullback.fst f t = (L.mul _ (prPt f t) (constPtR f t x)).1 :=
  pullback.lift_fst _ _ _


public theorem translate_over (x : SchemeHomOver t f) :
    translate f L t x ≫ (pullback.snd f t ≫ t) = pullback.snd f t ≫ t := by
  rw [← Category.assoc, translate_snd]


public theorem constPtR_one : constPtR f t (L.one t) = L.one _ :=
  L.one_natural t _ (pullback.snd f t) rfl


public theorem constPtR_mul (x y : SchemeHomOver t f) :
    constPtR f t (L.mul t x y) = L.mul _ (constPtR f t x) (constPtR f t y) :=
  L.mul_natural t _ (pullback.snd f t) rfl x y


public theorem translate_one : translate f L t (L.one t) = 𝟙 (pullback f t) := by
  apply pullback.hom_ext
  · rw [translate_fst, constPtR_one, L.mul_one, Category.id_comp]; rfl
  · rw [translate_snd, Category.id_comp]


public theorem translate_mul (x y : SchemeHomOver t f) :
    translate f L t (L.mul t x y) = translate f L t x ≫ translate f L t y := by
  apply pullback.hom_ext
  · rw [translate_fst, Category.assoc, translate_fst, constPtR_mul]
    have hx := translate_over f L t x
    have e1 : translate f L t x ≫ (L.mul _ (prPt f t) (constPtR f t y)).1 =
        (schemeHomOverComp (translate f L t x) hx (L.mul _ (prPt f t) (constPtR f t y))).1 := rfl
    have e2 : schemeHomOverComp (translate f L t x) hx (prPt f t) = L.mul _ (prPt f t) (constPtR f t x) :=
      Subtype.ext (translate_fst f L t x)
    have e3 : schemeHomOverComp (translate f L t x) hx (constPtR f t y) = constPtR f t y :=
      Subtype.ext (show translate f L t x ≫ (pullback.snd f t ≫ y.1) = pullback.snd f t ≫ y.1 by
        rw [← Category.assoc, translate_snd])
    rw [e1, L.mul_natural, e2, e3, L.mul_assoc]
  · rw [translate_snd, Category.assoc, translate_snd, translate_snd]


public theorem translate_inv_mul (x : SchemeHomOver t f) :
    translate f L t (L.inv t x) ≫ translate f L t x = 𝟙 (pullback f t) := by
  rw [← translate_mul, L.inv_mul_cancel, translate_one]


public theorem translate_mul_inv (x : SchemeHomOver t f) :
    translate f L t x ≫ translate f L t (L.inv t x) = 𝟙 (pullback f t) := by
  rw [← translate_mul, L.mul_inv_cancel, translate_one]


@[simp] public theorem translateIso_hom (x : SchemeHomOver t f) : (translateIso f L t x).hom = translate f L t x := rfl

@[simp] public theorem translateIso_inv (x : SchemeHomOver t f) : (translateIso f L t x).inv = translate f L t (L.inv t x) := rfl


@[simp] public theorem baseScalarHom_apply (r : R) : baseScalarHom f t r = baseScalar f t r := rfl

namespace ThetaPt

variable {f} {L} {𝓛 : A.Modules} {t}


@[simp] public theorem mul_pt (θ θ' : ThetaPt f L 𝓛 t) : (θ * θ').pt = L.mul t θ.pt θ'.pt := rfl

@[simp] public theorem one_pt : (1 : ThetaPt f L 𝓛 t).pt = L.one t := rfl

@[simp] public theorem inv_pt (θ : ThetaPt f L 𝓛 t) : (θ⁻¹).pt = L.inv t θ.pt := rfl

public theorem div_def (θ θ' : ThetaPt f L 𝓛 t) : θ / θ' = θ * θ'⁻¹ := rfl

public theorem npow_zero (θ : ThetaPt f L 𝓛 t) : θ ^ (0 : ℕ) = 1 := rfl

public theorem npow_succ (θ : ThetaPt f L 𝓛 t) (n : ℕ) : θ ^ (n + 1) = θ ^ n * θ := rfl

public theorem zpow_ofNat (θ : ThetaPt f L 𝓛 t) (n : ℕ) : θ ^ (n : ℤ) = θ ^ n := rfl

public theorem zpow_negSucc (θ : ThetaPt f L 𝓛 t) (n : ℕ) : θ ^ (Int.negSucc n) = (θ ^ (n + 1))⁻¹ := rfl


public theorem mul_iso (θ θ' : ThetaPt f L 𝓛 t) : (θ * θ').iso =
    (Scheme.Modules.pullbackCongr (translate_mul f L t θ.pt θ'.pt)).app _ ≪≫
    ((Scheme.Modules.pullbackComp (translate f L t θ.pt) (translate f L t θ'.pt)).app _).symm ≪≫
    (Scheme.Modules.pullback (translate f L t θ.pt)).mapIso θ'.iso ≪≫ θ.iso := rfl


public theorem one_iso : (1 : ThetaPt f L 𝓛 t).iso =
    (Scheme.Modules.pullbackCongr (translate_one f L t)).app _ ≪≫ (Scheme.Modules.pullbackId _).app _ := rfl


@[simp] public theorem ofUnit_pt (u : Γ(pullback f t, ⊤)ˣ) : (ofUnit u : ThetaPt f L 𝓛 t).pt = L.one t := rfl

@[simp] public theorem ofScalar_pt (c : Rˣ) : (ofScalar c : ThetaPt f L 𝓛 t).pt = L.one t := rfl

public theorem ofUnit_iso (u : Γ(pullback f t, ⊤)ˣ) : (ofUnit u : ThetaPt f L 𝓛 t).iso =
    ((Scheme.Modules.pullbackCongr (translate_one f L t)).app _ ≪≫ (Scheme.Modules.pullbackId _).app _) ≪≫
      Scheme.Modules.homothetyIso _ u := rfl

public theorem ofScalar_eq (c : Rˣ) : (ofScalar c : ThetaPt f L 𝓛 t) = ofUnit (Units.map (baseScalarHom f t).toMonoidHom c) := rfl


public theorem toAut_mul (θ θ' : ThetaPt f L 𝓛 t) : toAut (θ * θ') = toAut θ ≪≫ toAut θ' :=
  Scheme.Modules.fibration.autOfIso_trans _ (translateIso f L t θ.pt) (translateIso f L t θ'.pt)
    (translateIso f L t (L.mul t θ.pt θ'.pt)) (translate_mul f L t θ.pt θ'.pt) θ.iso θ'.iso


public theorem toAut_one : toAut (1 : ThetaPt f L 𝓛 t) = Iso.refl _ :=
  Scheme.Modules.fibration.autOfIso_refl _ _ _


public theorem toAut_inv_trans (θ : ThetaPt f L 𝓛 t) : toAut θ⁻¹ ≪≫ toAut θ = Iso.refl _ :=
  Scheme.Modules.fibration.autOfIso_symm_trans _ (translateIso f L t θ.pt) (translateIso f L t (L.inv t θ.pt))
    (translate_inv_mul f L t θ.pt) θ.iso


public theorem eq_of_toGrp_eq (θ θ' : ThetaPt f L 𝓛 t) (h : toGrp θ = toGrp θ') : θ = θ' := by
  obtain ⟨x, ψ⟩ := θ
  obtain ⟨x', ψ'⟩ := θ'
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
  change x = x' at h2
  subst h2
  have h3 : ψ = ψ' :=
    Scheme.Modules.fibration.autOfIso_injective _ (translateIso f L t x) ψ ψ' (MulOpposite.op_injective h1)
  subst h3
  rfl


public theorem toGrp_injective : Function.Injective (toGrp (f := f) (L := L) (𝓛 := 𝓛) (t := t)) :=
  fun θ θ' h => eq_of_toGrp_eq θ θ' h


public theorem toGrp_mul (θ θ' : ThetaPt f L 𝓛 t) : toGrp (θ * θ') = toGrp θ * toGrp θ' := by
  refine Prod.ext ?_ rfl
  show MulOpposite.op (toAut (θ * θ')) = MulOpposite.op (toAut θ) * MulOpposite.op (toAut θ')
  rw [← MulOpposite.op_mul, toAut_mul, Aut.Aut_mul_def]


public theorem toGrp_one : toGrp (1 : ThetaPt f L 𝓛 t) = 1 := by
  refine Prod.ext ?_ rfl
  show MulOpposite.op (toAut 1) = 1
  rw [toAut_one]; rfl


public theorem toGrp_inv (θ : ThetaPt f L 𝓛 t) : toGrp θ⁻¹ = (toGrp θ)⁻¹ := by
  refine Prod.ext ?_ rfl
  show MulOpposite.op (toAut θ⁻¹) = (MulOpposite.op (toAut θ))⁻¹
  rw [← MulOpposite.op_inv]
  congr 1
  symm
  apply inv_eq_of_mul_eq_one_right
  rw [Aut.Aut_mul_def]
  exact toAut_inv_trans θ


public theorem toGrp_div (θ θ' : ThetaPt f L 𝓛 t) : toGrp (θ / θ') = toGrp θ / toGrp θ' := by
  rw [div_def, toGrp_mul, toGrp_inv, div_eq_mul_inv]


public theorem toGrp_npow (θ : ThetaPt f L 𝓛 t) (n : ℕ) : toGrp (θ ^ n) = toGrp θ ^ n := by
  induction n with
  | zero => rw [npow_zero, toGrp_one, pow_zero]
  | succ n ih => rw [npow_succ, toGrp_mul, ih, pow_succ]


public theorem toGrp_zpow (θ : ThetaPt f L 𝓛 t) (n : ℤ) : toGrp (θ ^ n) = toGrp θ ^ n := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_ofNat, toGrp_npow, zpow_natCast]
  | negSucc n => rw [zpow_negSucc, toGrp_inv, toGrp_npow, _root_.zpow_negSucc]


@[simp] public theorem ptHom_apply (θ : ThetaPt f L 𝓛 t) : ptHom θ = θ.pt := rfl

