import Mathlib
import Def.AlgebraicGeometry_OrderedAffineCoverCech
import Def.AlgebraicGeometry_OrderedAffineCoverOf
import Instance.AlgebraicGeometry_OModulePresheafLerayBicomplex
import Abbrev.AlgebraicGeometry_OModulePresheafLerayBicomplex

set_option autoImplicit false

noncomputable section

namespace AlgebraicGeometry.OModulePresheaf.Leray

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Scheme

section FiberAffine

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}

def restrictToPreimage
    (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R)) [IsSeparated πZ]
    (K' : Scheme.OrderedAffineCover V') {U : Z.Opens} (hU : IsAffineOpen U) :
    Scheme.OrderedAffineCoverOf ((Opens.map p.base).obj U) where
  ι := K'.ι
  U := fun i => K'.U i ⊓ (Opens.map p.base).obj U
  isAffineOpen := fun i => Scheme.OrderedAffineCover.fiberAffineOpen p πZ (K'.isAffineOpen i) hU
  le := fun _ => inf_le_right
  iSup_eq := by rw [← iSup_inf_eq, K'.iSup_eq_top, top_inf_eq]

end FiberAffine

section LerayDC

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R))
variable (K : Scheme.OrderedAffineCover Z) (K' : Scheme.OrderedAffineCover V')

def dH (a b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    biC p πZ K K' a b →ₗ[R] biC p πZ K K' (a + 1) b :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  LinearMap.pi fun στ => ∑ j : Fin (a + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((Scheme.OrderedAffineCoverOf.res (p ≫ πZ)
      (inf_le_inf_left _ ((Opens.map p.base).monotone
        (K.inter_le_inter_face στ.1 j)))).comp
      (LinearMap.proj (R := R) (⟨K.face στ.1 j, στ.2⟩ :
        BiIdx K K' a b)))

def dV (a b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    biC p πZ K K' a b →ₗ[R] biC p πZ K K' a (b + 1) :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  LinearMap.pi fun στ => ∑ j : Fin (b + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((Scheme.OrderedAffineCoverOf.res (p ≫ πZ)
      (inf_le_inf_right _ (K'.inter_le_inter_face στ.2 j))).comp
      (LinearMap.proj (R := R) (⟨στ.1, K'.face στ.2 j⟩ :
        BiIdx K K' a b)))

end LerayDC

section RelAlt

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R))
variable (K' : Scheme.OrderedAffineCover V')

def relAltd (U : Z.Opens) (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    relAltC p πZ K' U b →ₗ[R] relAltC p πZ K' U (b + 1) :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  LinearMap.pi fun τ => ∑ j : Fin (b + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((Scheme.OrderedAffineCoverOf.res (p ≫ πZ)
      (inf_le_inf_right _ (K'.inter_le_inter_face τ j))).comp
      (LinearMap.proj (R := R) (K'.face τ j)))

def relAltHB (U : Z.Opens) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    (b : ℕ) → Submodule R (LinearMap.ker (relAltd p πZ K' U b)) :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  fun b => match b with
  | 0 => ⊥
  | b' + 1 => (LinearMap.range (relAltd p πZ K' U b')).comap
      (LinearMap.ker (relAltd p πZ K' U (b' + 1))).subtype

abbrev relAltH (U : Z.Opens) (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    Type u :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  LinearMap.ker (relAltd p πZ K' U b) ⧸ relAltHB p πZ K' U b

def pushOpen (U : Z.Opens) : OModulePresheaf (p ≫ πZ) where
  obj W := Γ(V', W ⊓ (Opens.map p.base).obj U)
  addCommGroup _ := inferInstance
  moduleSections W := Module.compHom _
    (V'.presheaf.map (homOfLE (inf_le_left : W ⊓ (Opens.map p.base).obj U ≤ W)).op).hom
  isScalarTower W := by
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ) W
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ) (W ⊓ (Opens.map p.base).obj U)
    letI : Module Γ(V', W) Γ(V', W ⊓ (Opens.map p.base).obj U) := Module.compHom _
      (V'.presheaf.map (homOfLE (inf_le_left : W ⊓ (Opens.map p.base).obj U ≤ W)).op).hom
    refine ⟨fun r a x => ?_⟩
    show (V'.presheaf.map (homOfLE (inf_le_left (b := (Opens.map p.base).obj U))).op).hom
          ((V'.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
            ((p ≫ πZ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) * a) * x
      = (V'.presheaf.map (homOfLE (le_top : W ⊓ (Opens.map p.base).obj U ≤ ⊤)).op).hom
            ((p ≫ πZ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
          * ((V'.presheaf.map (homOfLE inf_le_left).op).hom a * x)
    rw [map_mul, ← mul_assoc, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp,
      homOfLE_comp]
  res h := Scheme.OrderedAffineCoverOf.res (p ≫ πZ) (inf_le_inf_right _ h)
  res_smul {W W'} h a x := by
    show (V'.presheaf.map (homOfLE (inf_le_inf_right ((Opens.map p.base).obj U) h)).op).hom
          ((V'.presheaf.map (homOfLE inf_le_left).op).hom a * x)
      = (V'.presheaf.map (homOfLE inf_le_left).op).hom ((V'.presheaf.map (homOfLE h).op).hom a)
          * (V'.presheaf.map (homOfLE (inf_le_inf_right _ h)).op).hom x
    rw [map_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, ← op_comp, ← op_comp, homOfLE_comp, homOfLE_comp]
  res_refl W := (OModulePresheaf.unit (p ≫ πZ)).res_refl _
  res_comp h h' := (OModulePresheaf.unit (p ≫ πZ)).res_comp _ _

def pullOpen (W : V'.Opens) : OModulePresheaf πZ where
  obj U := Γ(V', W ⊓ (Opens.map p.base).obj U)
  addCommGroup _ := inferInstance
  moduleSections U := Module.compHom _
    (p.appLE U (W ⊓ (Opens.map p.base).obj U) inf_le_right).hom
  isScalarTower U := by
    letI := Scheme.OrderedAffineCoverOf.moduleSections πZ U
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ) (W ⊓ (Opens.map p.base).obj U)
    letI : Module Γ(Z, U) Γ(V', W ⊓ (Opens.map p.base).obj U) :=
      Module.compHom _ (p.appLE U (W ⊓ (Opens.map p.base).obj U) inf_le_right).hom
    refine ⟨fun r a x => ?_⟩

    show (p.appLE U (W ⊓ (Opens.map p.base).obj U) inf_le_right).hom
          ((Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
            ((πZ.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) * a) * x
      = (V'.presheaf.map (homOfLE (le_top : W ⊓ (Opens.map p.base).obj U ≤ ⊤)).op).hom
            (((p ≫ πZ).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
          * ((p.appLE U (W ⊓ (Opens.map p.base).obj U) inf_le_right).hom a * x)
    rw [map_mul, ← mul_assoc]
    congr 2

    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  res h := Scheme.OrderedAffineCoverOf.res (p ≫ πZ) (inf_le_inf_left W ((Opens.map p.base).monotone h))
  res_smul {U U'} h a x := by
    show (V'.presheaf.map (homOfLE (inf_le_inf_left W ((Opens.map p.base).monotone h))).op).hom
          ((p.appLE U' (W ⊓ (Opens.map p.base).obj U') inf_le_right).hom a * x)
      = (p.appLE U (W ⊓ (Opens.map p.base).obj U) inf_le_right).hom
            ((Z.presheaf.map (homOfLE h).op).hom a)
          * (V'.presheaf.map (homOfLE (inf_le_inf_left W ((Opens.map p.base).monotone h))).op).hom x
    rw [map_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply (f := Z.presheaf.map _),
      Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  res_refl U := (OModulePresheaf.unit (p ≫ πZ)).res_refl _
  res_comp h h' := (OModulePresheaf.unit (p ≫ πZ)).res_comp _ _

def relRes {U U' : Z.Opens} (h : U ≤ U') (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    relAltC p πZ K' U' b →ₗ[R] relAltC p πZ K' U b :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  LinearMap.pi fun τ => (Scheme.OrderedAffineCoverOf.res (p ≫ πZ)
    (inf_le_inf_left (K'.inter τ) ((Opens.map p.base).monotone h))).comp (LinearMap.proj τ)

def relResKer {U U' : Z.Opens} (h : U ≤ U') (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    LinearMap.ker (relAltd p πZ K' U' b) →ₗ[R] LinearMap.ker (relAltd p πZ K' U b) :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  (relRes p πZ K' h b).restrict fun f hf => LinearMap.mem_ker.mpr <| by
    rw [← LinearMap.comp_apply, ← relRes_comm, LinearMap.comp_apply, LinearMap.mem_ker.mp hf, map_zero]

def relHPresheaf (b : ℕ) : OModulePresheaf πZ where
  obj U := relAltH p πZ K' U b
  addCommGroup _ :=
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    inferInstance
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    inferInstance
  moduleSections U := relAltH_modΓ p πZ K' U b
  isScalarTower U := relAltH_scalarTower p πZ K' U b
  res {U U'} h :=
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    Submodule.mapQ _ _ (relResKer p πZ K' h b) (relAltHB_res_le p πZ K' h b)
  res_smul {U U'} h a z := by

    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    induction z using Quotient.inductionOn' with | _ x => ?_
    exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun τ =>
      (pullOpen p πZ (K'.inter τ)).res_smul h a (x.1 τ)))
  res_refl U := by
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    refine LinearMap.ext fun z => z.inductionOn' fun x =>
      congrArg Submodule.Quotient.mk (Subtype.ext (funext fun τ => ?_))
    exact LinearMap.congr_fun ((OModulePresheaf.unit (p ≫ πZ)).res_refl _) (x.1 τ)
  res_comp {U U' U''} h h' := by
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    refine LinearMap.ext fun z => z.inductionOn' fun x =>
      congrArg Submodule.Quotient.mk (Subtype.ext (funext fun τ => ?_))
    exact LinearMap.congr_fun ((OModulePresheaf.unit (p ≫ πZ)).res_comp
      (inf_le_inf_left _ ((Opens.map p.base).monotone h))
      (inf_le_inf_left _ ((Opens.map p.base).monotone h'))) (x.1 τ)

end RelAlt

section E2Iso

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R))
variable (K : Scheme.OrderedAffineCover Z) (K' : Scheme.OrderedAffineCover V')

def biC_uncurry (a b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    biC p πZ K K' a b ≃ₗ[R]
      ∀ σ : K.Idx a,
        relAltC p πZ K' (K.inter σ) b :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  { toFun := fun f σ τ => f (σ, τ)
    invFun := fun g στ => g στ.1 στ.2
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

def biC_uncurry' (a b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    biC p πZ K K' a b ≃ₗ[R]
      ∀ τ : K'.Idx b,
        OModulePresheaf.cochain (pullOpen p πZ (K'.inter τ))
          K a :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  { toFun := fun f τ σ => f (σ, τ)
    invFun := fun g στ => g στ.2 στ.1
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

end E2Iso

end AlgebraicGeometry.OModulePresheaf.Leray

end
