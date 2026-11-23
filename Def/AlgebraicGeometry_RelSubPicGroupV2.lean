import Mathlib
import Def.AlgebraicGeometry_RelativePicardFunctor
import Def.AlgebraicGeometry_RepresentsRelSubPic
import Def.AlgebraicGeometry_RelSubPicPresheaf
import Lemma.Scheme.RelativeGroupLawGrpObj
import Structure.JacJ1Iface
import Abbrev.SheafOfModules_MonoidalV2
import Def.AlgebraicGeometry_RelSubPicGroup
import Instance.AlgebraicGeometry_RelSubPicGroupV2
import Structure.AlgebraicGeometry_RelSubPicGroupV2

section InlinedTheorems

section LinkageInlined_5b3a613b

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v' u'

open CategoryTheory MonoidalCategory Limits Opposite

noncomputable section

namespace PresheafOfModules

namespace InternalHom

variable {C : Type u'} [Category.{v'} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F N : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

private noncomputable def toPresheafHom (X : Cᵒᵖ) (φ : naturalFamilies F N X) :
    (presheafHom F.presheaf N.presheaf).obj X where
  app Y := AddCommGrpCat.ofHom (φ.1 Y.unop.hom.op).toAddMonoidHom
  naturality {Y Y'} k := by
    ext x
    change φ.1 Y'.unop.hom.op (F.map k.unop.left.op x) = N.map k.unop.left.op (φ.1 Y.unop.hom.op x)
    rw [φ.2 Y.unop.hom.op k.unop.left.op x]
    exact congr_app φ (by rw [← op_comp, Over.w]) _

variable {F N} in

private abbrev appAt {X : Cᵒᵖ} (s : (presheafHom F.presheaf N.presheaf).obj X) (Y : (Over X.unop)ᵒᵖ)
    (x : F.obj (Opposite.op Y.unop.left)) : N.obj (Opposite.op Y.unop.left) :=
  s.app Y x

private noncomputable def linearSub : Subfunctor (presheafHom F.presheaf N.presheaf) where
  obj X := { s | ∀ (Y : (Over X.unop)ᵒᵖ) (r : R.obj (Opposite.op Y.unop.left))
    (x : F.obj (Opposite.op Y.unop.left)), appAt s Y (r • x) = r • appAt s Y x }
  map h _ hs Y r x := hs (Opposite.op ((Over.map h.unop).obj Y.unop)) r x

private noncomputable def ofPresheafHom (X : Cᵒᵖ) (s : (linearSub F N).obj X) : naturalFamilies F N X :=
  ⟨fun Y f =>
    { toFun := fun x => appAt s.1 (Opposite.op (Over.mk f.unop)) x
      map_add' := fun x x' => (s.1.app _).hom.map_add _ _
      map_smul' := fun r x => s.2 (Opposite.op (Over.mk f.unop)) r x }, by
    intro Y Z f g x
    change N.map g (appAt s.1 (Opposite.op (Over.mk f.unop)) x) =
      appAt s.1 (Opposite.op (Over.mk (g.unop ≫ f.unop))) (F.map g x)
    have := s.1.naturality (Over.homMk g.unop rfl : Over.mk (g.unop ≫ f.unop) ⟶ Over.mk f.unop).op
    exact (ConcreteCategory.congr_hom this x).symm⟩

private noncomputable def equivLinearSub (X : Cᵒᵖ) : naturalFamilies F N X ≃ (linearSub F N).obj X where
  toFun φ := ⟨toPresheafHom F N X φ, fun Y r x => (φ.1 Y.unop.hom.op).map_smul r x⟩
  invFun s := ofPresheafHom F N X s
  left_inv φ := by
    apply naturalFamilies_ext; intro Y f x; rfl
  right_inv s := by rfl

private noncomputable def isoLinearSub :
    InternalHom.presheaf F N ⋙ forget AddCommGrpCat ≅ (linearSub F N).toFunctor :=
  NatIso.ofComponents (fun X => (equivLinearSub F N X).toIso) (by intros; rfl)

variable {F N}

end InternalHom

end PresheafOfModules

end

end LinkageInlined_5b3a613b

section LinkageInlined_68107509

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Limits

noncomputable section

namespace PresheafOfModules.IsMonoidalW

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (R : Sheaf J RingCat.{u})
  (α : 𝒪 ⋙ forget₂ CommRingCat RingCat ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

private abbrev PMod := PresheafOfModules.{u} (𝒪 ⋙ forget₂ CommRingCat RingCat)

private abbrev W : MorphismProperty (PMod 𝒪) :=
  (J.W (A := AddCommGrpCat.{u})).inverseImage
    (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat))

private abbrev shf : PMod 𝒪 ⥤ SheafOfModules.{u} R := PresheafOfModules.sheafification α

private abbrev inc : SheafOfModules.{u} R ⥤ PMod 𝒪 :=
  SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α

private abbrev adj : shf 𝒪 R α ⊣ inc 𝒪 R α := PresheafOfModules.sheafificationAdjunction α

end PresheafOfModules.IsMonoidalW

end


end LinkageInlined_68107509

section LinkageInlined_7e0d42f8

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry Scheme

namespace AlgebraicGeometry.Scheme.Modules

private noncomputable def trivializationOfLE {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) (L : X.Modules)
    (e : (Modules.pullback U.ι).obj L ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :
    (Modules.pullback V.ι).obj L ≅ SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf :=
  (Modules.pullbackCongr (X.homOfLE_ι h).symm).app L ≪≫
    ((Modules.pullbackComp (X.homOfLE h) U.ι).symm).app L ≪≫
    (Modules.pullback (X.homOfLE h)).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso (X.homOfLE h)

end AlgebraicGeometry.Scheme.Modules

end LinkageInlined_7e0d42f8

section LinkageInlined_23d4f55a

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory Limits

namespace PresheafOfModules

namespace InvertibleDual

open Opposite InternalHom TensorProduct

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

private noncomputable abbrev dual : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) :=
  ihomObj F (𝟙_ _)

private noncomputable abbrev ev : F ⊗ dual F ⟶ 𝟙_ _ := uncurry' F (𝟙 (dual F))


variable {F} {X₀ : Cᵒᵖ} (D : TrivializationBelow F X₀)

namespace TrivializationBelow

private noncomputable def restrictTo {Y : Cᵒᵖ} (f : X₀ ⟶ Y) : TrivializationBelow F Y where
  gen g := D.gen (f ≫ g)
  compat g g' := by rw [D.compat, Category.assoc]
  bij g := D.bij (f ≫ g)

private noncomputable def triv {Y : Cᵒᵖ} (f : X₀ ⟶ Y) : R.obj Y ≃ₗ[R.obj Y] F.obj Y :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton (R.obj Y) (F.obj Y) (D.gen f)) (D.bij f)

private noncomputable def coord {Y : Cᵒᵖ} (f : X₀ ⟶ Y) : F.obj Y →ₗ[R.obj Y] R.obj Y := (D.triv f).symm

private noncomputable def dualGen : (dual F).obj X₀ :=
  ⟨fun Y f => D.coord f, fun Y Z f g x => by
    change R.map g (D.coord f x) = D.coord (f ≫ g) (F.map g x)
    rw [D.coord_map]⟩

private noncomputable def evInv : R.obj X₀ →ₗ[R.obj X₀] (F.obj X₀ ⊗[R.obj X₀] (dual F).obj X₀) :=
  LinearMap.toSpanSingleton _ _ (D.gen (𝟙 X₀) ⊗ₜ D.dualGen)

omit D in
end TrivializationBelow


end InvertibleDual

end PresheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

open TopologicalSpace Opposite PresheafOfModules.InvertibleDual

variable {X : Scheme.{u}}

private noncomputable def trivializationOfLE_23d4f55a {U V : X.Opens} (h : V ≤ U) (L : X.Modules)
    (e : (Modules.pullback U.ι).obj L ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :
    (Modules.pullback V.ι).obj L ≅ SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf :=
  (Modules.pullbackCongr (X.homOfLE_ι h).symm).app L ≪≫
    ((Modules.pullbackComp (X.homOfLE h) U.ι).symm).app L ≪≫
    (Modules.pullback (X.homOfLE h)).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso (X.homOfLE h)

private noncomputable def dualSheaf (L : X.Modules) : X.Modules where
  val := PresheafOfModules.ihomObj L.val (𝟙_ X.PresheafOfModules)
  isSheaf := PresheafOfModules.isSheaf_ihomObj_loc L.val _ (SheafOfModules.unit X.ringCatSheaf).isSheaf

variable (U : X.Opens)

private noncomputable def restrictRingCatSheafHom : (U : Scheme.{u}).ringCatSheaf ⟶
    (U.ι.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology (U : Scheme.{u})) (Opens.grothendieckTopology X)).obj
        X.ringCatSheaf :=
  ⟨𝟙 _⟩

private noncomputable def restrictFunctor' : X.Modules ⥤ (U : Scheme.{u}).Modules :=
  SheafOfModules.pushforward (restrictRingCatSheafHom U)

private noncomputable def restrictFunctor'IsoPullback : restrictFunctor' U ≅ Modules.pullback U.ι :=
  eqToIso (restrictFunctor'_eq U) ≪≫ restrictFunctorIsoPullback U.ι

variable {U} (L : X.Modules)

section

variable (e : (restrictFunctor' U).obj L ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)

private noncomputable def gen₀ (W : (U : Scheme.{u}).Opens) : L.val.obj (op (U.ι ''ᵁ W)) :=
  (e.inv.val.app (op W)).hom (1 : Γ(U, W))

private noncomputable def trivializationBelow : TrivializationBelow L.val (op U) where
  gen {Y} f := L.val.map (eqToHom (image_preimage_of_le (U := U) f.unop.le).symm :
      Y.unop ⟶ U.ι ''ᵁ (U.ι ⁻¹ᵁ Y.unop)).op (gen₀ L e (U.ι ⁻¹ᵁ Y.unop))
  compat {Y Z} f g := by
    have hle : U.ι ⁻¹ᵁ Z.unop ≤ U.ι ⁻¹ᵁ Y.unop := fun x hx => g.unop.le hx
    dsimp only
    rw [← gen₀_map L e (homOfLE hle)]
    erw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
    exact congrFun (congrArg
      (fun φ : (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ Y.unop)) ⟶ Z) =>
        ((L.val.map φ).hom : L.val.obj (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ Y.unop))) → L.val.obj Z))
      (Subsingleton.elim _ _)) _
  bij {Y} f := bijective_smul_map_eqToHom L (image_preimage_of_le (U := U) f.unop.le) _
    (gen₀_bijective L e _)

end

private def trivSieve (V : X.Opens) : Sieve V where
  arrows W _ := Nonempty (TrivializationBelow L.val (op W))
  downward_closed {W W'} f hf g := by
    obtain ⟨D⟩ := hf
    exact ⟨D.restrictTo g.op⟩

private noncomputable def tensorDualSheafIso (L : X.Modules) [Fact (Scheme.Modules.IsInvertible L)] :
    L ⊗ dualSheaf L ≅ 𝟙_ X.Modules :=
  (Scheme.Modules.tensorIsoSheafify L (dualSheaf L)).symm ≪≫
    asIso ((Modules.sheafify X).map (ev (R := X.sheaf.obj) L.val)) ≪≫
    SheafOfModules.sheafifyUnitIso X.sheaf.obj X.ringCatSheaf.property

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules in Scheme

end LinkageInlined_23d4f55a

end InlinedTheorems

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard Scheme
  NeronModelInfra GoodReductionJacobian

open scoped CategoryTheory.MonObj

noncomputable section

namespace AlgebraicGeometry.RelPicard

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

end AlgebraicGeometry.RelPicard

end
