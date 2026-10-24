import Mathlib

import Lemma.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Mathlib.Algebra.Module.Submodule.RestrictScalars

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

universe u

namespace AlgebraicGeometry.OModulePresheaf

open CategoryTheory Opposite TopologicalSpace

section IdealSmulInfra

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

def IdealAnnihilates (I : V.IdealSheafData) (F : OModulePresheaf π) : Prop :=
  ∀ U : V.affineOpens, ∀ a ∈ I.ideal U, ∀ x : F.obj U.1, a • x = 0

def idealSections (I : V.IdealSheafData) (U : V.Opens) : Ideal Γ(V, U) :=
  RingHom.ker (I.subschemeι.app U).hom

theorem idealSections_eq_ideal (I : V.IdealSheafData) (U : V.affineOpens) :
    idealSections I U.1 = I.ideal U :=
  I.ker_subschemeι_app U

theorem idealSections_res (I : V.IdealSheafData) {U U' : V.Opens} (h : U ≤ U')
    (a : Γ(V, U')) (ha : a ∈ idealSections I U') :
    (V.presheaf.map (homOfLE h).op).hom a ∈ idealSections I U := by
  show (I.subschemeι.app U).hom ((V.presheaf.map (homOfLE h).op).hom a) = 0
  rw [← CommRingCat.comp_apply, I.subschemeι.naturality, CommRingCat.comp_apply,
    show (I.subschemeι.app U').hom a = 0 from ha, map_zero]

theorem idealSections_pow_res (I : V.IdealSheafData) (k : ℕ)
    {U U' : V.Opens} (h : U ≤ U') (a : Γ(V, U'))
    (ha : a ∈ idealSections I U' ^ k) :
    (V.presheaf.map (homOfLE h).op).hom a ∈ idealSections I U ^ k := by
  have hle : (idealSections I U').map (V.presheaf.map (homOfLE h).op).hom
      ≤ idealSections I U :=
    Ideal.map_le_iff_le_comap.mpr fun b hb => idealSections_res I h b hb
  have hmap : ∀ m, (idealSections I U' ^ m).map (V.presheaf.map (homOfLE h).op).hom
      ≤ idealSections I U ^ m := by
    intro m
    rw [Ideal.map_pow]
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_succ]; exact Ideal.mul_mono ih hle
  exact hmap k (Ideal.mem_map_of_mem _ ha)

def idealPowSub (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ)
    (U : V.Opens) : Submodule R (F.obj U) :=
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule; haveI := F.isScalarTower U
  (idealSections I U ^ k • (⊤ : Submodule Γ(V, U) (F.obj U))).restrictScalars R

theorem idealPowSub_res (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ)
    {U U' : V.Opens} (h : U ≤ U') (x : F.obj U')
    (hx : x ∈ idealPowSub π I F k U') :
    F.res h x ∈ idealPowSub π I F k U := by
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U').toModule; haveI := F.isScalarTower U'
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule; haveI := F.isScalarTower U
  rw [idealPowSub, Submodule.restrictScalars_mem] at hx ⊢
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y _
    rw [F.res_smul h a y]
    exact Submodule.smul_mem_smul (idealSections_pow_res I k h a ha) trivial
  · intro y z hy hz; rw [map_add]; exact add_mem hy hz

def idealPow (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ) :
    OModulePresheaf π where
  obj U := idealPowSub π I F k U
  addCommGroup U := inferInstance
  module U := inferInstance
  moduleSections U :=
    letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule; haveI := F.isScalarTower U
    inferInstanceAs (Module Γ(V, U)
      ((idealSections I U ^ k • (⊤ : Submodule _ _)).restrictScalars R))
  isScalarTower U := by
    letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule; haveI := F.isScalarTower U
    exact inferInstanceAs (IsScalarTower R Γ(V, U)
      ((idealSections I U ^ k • (⊤ : Submodule _ _)).restrictScalars R))
  res {U U'} h := LinearMap.codRestrict (idealPowSub π I F k U)
    ((F.res h).comp (idealPowSub π I F k U').subtype)
    (fun x => idealPowSub_res π I F k h x.1 x.2)
  res_smul {U U'} h a x := by
    letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U').toModule; haveI := F.isScalarTower U'
    letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule; haveI := F.isScalarTower U
    exact Subtype.ext (F.res_smul h a x.1)
  res_refl U := LinearMap.ext fun x =>
    Subtype.ext (LinearMap.congr_fun (F.res_refl U) x.1)
  res_comp {U U' U''} h h' := LinearMap.ext fun x =>
    Subtype.ext (LinearMap.congr_fun (F.res_comp h h') x.1)

theorem mem_idealPowSub_iff_of_affine (I : V.IdealSheafData) (F : OModulePresheaf π)
    (k : ℕ) (U : V.affineOpens) (x : F.obj U.1) :
    (⟨x, Submodule.mem_top⟩ : (⊤ : Submodule R (F.obj U.1))).1 ∈
        idealPowSub π I F k U.1
      ↔ x ∈ (I.ideal U ^ k • (⊤ : Submodule Γ(V, U.1) (F.obj U.1))) := by
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U.1).toModule; haveI := F.isScalarTower U.1
  rw [idealPowSub, Submodule.restrictScalars_mem,
    idealSections_eq_ideal]

end IdealSmulInfra

section QuotPMod

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

theorem idealPowSub_antitone (I : V.IdealSheafData) (F : OModulePresheaf π)
    {k k' : ℕ} (h : k ≤ k') (U : V.Opens) :
    idealPowSub π I F k' U ≤ idealPowSub π I F k U := by
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule; haveI := F.isScalarTower U
  exact fun x hx => Submodule.smul_mono (Ideal.pow_le_pow_right h) le_rfl hx

def idealPowSuccSub (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ) (U : V.Opens) :
    Submodule R ((idealPow π I F k).obj U) :=
  (idealPowSub π I F (k + 1) U).comap
    (idealPowSub π I F k U).subtype

theorem idealPowSub_smul_mem (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ)
    (U : V.Opens) (a : Γ(V, U)) (x : F.obj U)
    (hx : x ∈ idealPowSub π I F k U) :
    a • x ∈ idealPowSub π I F k U := by
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule; haveI := F.isScalarTower U
  rw [idealPowSub, Submodule.restrictScalars_mem] at hx ⊢
  exact Submodule.smul_mem _ a hx

theorem idealPowSuccSub_smul_mem (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ)
    (U : V.Opens) (a : Γ(V, U)) (x : (idealPow π I F k).obj U)
    (hx : x ∈ idealPowSuccSub π I F k U) :
    a • x ∈ idealPowSuccSub π I F k U := by
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule; haveI := F.isScalarTower U
  rw [idealPowSuccSub, Submodule.mem_comap, idealPowSub,
    Submodule.restrictScalars_mem] at hx ⊢
  exact Submodule.smul_mem _ a hx

@[reducible]
def idealPowQuotModuleSections (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ) (U : V.Opens) :
    Module Γ(V, U) ((idealPow π I F k).obj U
      ⧸ idealPowSuccSub π I F k U) := by
  set p := idealPowSuccSub π I F k U
  letI : SMul Γ(V, U) (_ ⧸ p) :=
    { smul := fun a => Quotient.map' (a • ·) fun x y h => by
        rw [Submodule.quotientRel_def] at h ⊢
        rw [← smul_sub]; exact idealPowSuccSub_smul_mem π I F k U a (x - y) h }
  have key : ∀ (a : Γ(V, U)) (y : (idealPow π I F k).obj U),
      a • p.mkQ y = p.mkQ (a • y) := fun _ _ => rfl
  exact
  { smul := (· • ·)
    one_smul := fun x => by
      obtain ⟨y, rfl⟩ := p.mkQ_surjective x; rw [key, one_smul]
    mul_smul := fun a b x => by
      obtain ⟨y, rfl⟩ := p.mkQ_surjective x; rw [key, key, key, mul_smul]
    smul_zero := fun a => by rw [← map_zero p.mkQ, key, smul_zero]
    smul_add := fun a x₁ x₂ => by
      obtain ⟨y₁, rfl⟩ := p.mkQ_surjective x₁; obtain ⟨y₂, rfl⟩ := p.mkQ_surjective x₂
      rw [← map_add, key, smul_add, map_add, key, key]
    add_smul := fun a b x => by
      obtain ⟨y, rfl⟩ := p.mkQ_surjective x; rw [key, key, key, ← map_add, add_smul]
    zero_smul := fun x => by
      obtain ⟨y, rfl⟩ := p.mkQ_surjective x; rw [key, zero_smul, map_zero] }

theorem idealPowQuot_smul_mk (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ)
    (U : V.Opens) (a : Γ(V, U)) (y : (idealPow π I F k).obj U) :
    letI := idealPowQuotModuleSections π I F k U
    a • (idealPowSuccSub π I F k U).mkQ y
      = (idealPowSuccSub π I F k U).mkQ (a • y) :=
  rfl

def idealPowQuot (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ) :
    OModulePresheaf π where
  obj U := (idealPow π I F k).obj U ⧸ idealPowSuccSub π I F k U
  addCommGroup U := inferInstance
  module U := inferInstance
  moduleSections U := idealPowQuotModuleSections π I F k U
  isScalarTower U := by
    letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule; letI := idealPowQuotModuleSections π I F k U
    refine ⟨fun r a x => ?_⟩
    obtain ⟨y, rfl⟩ := (idealPowSuccSub π I F k U).mkQ_surjective x
    rw [idealPowQuot_smul_mk, idealPowQuot_smul_mk, ← map_smul]
    exact congrArg _
      ((idealPow π I F k).isScalarTower U |>.smul_assoc r a y)
  res {U U'} h := Submodule.mapQ _ _ ((idealPow π I F k).res h)
    (fun x hx => idealPowSub_res π I F (k + 1) h _ hx)
  res_smul {U U'} h a x := by
    letI := idealPowQuotModuleSections π I F k U'
    letI := idealPowQuotModuleSections π I F k U
    obtain ⟨y, rfl⟩ := (idealPowSuccSub π I F k U').mkQ_surjective x
    rw [idealPowQuot_smul_mk]
    show (idealPowSuccSub π I F k U).mkQ
        ((idealPow π I F k).res h (a • y)) = _
    rw [(idealPow π I F k).res_smul h a y, ← idealPowQuot_smul_mk]
    rfl
  res_refl U := LinearMap.ext fun x => by
    obtain ⟨y, rfl⟩ := (idealPowSuccSub π I F k U).mkQ_surjective x
    exact congrArg ((idealPowSuccSub π I F k U).mkQ)
      (LinearMap.congr_fun ((idealPow π I F k).res_refl U) y)
  res_comp {U U' U''} h h' := LinearMap.ext fun x => by
    obtain ⟨y, rfl⟩ := (idealPowSuccSub π I F k U'').mkQ_surjective x
    exact congrArg ((idealPowSuccSub π I F k U).mkQ)
      (LinearMap.congr_fun ((idealPow π I F k).res_comp h h') y)

def idealPowSuccInc (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ) :
    OModulePresheaf.AffHom (idealPow π I F (k + 1))
      (idealPow π I F k) where
  app U := Submodule.inclusion
    (idealPowSub_antitone π I F k.le_succ U.1)
  app_smul U a x := rfl
  naturality {U U'} h := LinearMap.ext fun x => Subtype.ext rfl

def idealPowSES (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ) :
    OModulePresheaf.AffSES (idealPow π I F (k + 1))
      (idealPow π I F k) (idealPowQuot π I F k) where
  inc := idealPowSuccInc π I F k
  proj :=
    { app := fun U => (idealPowSuccSub π I F k U.1).mkQ
      app_smul := fun U a y => (idealPowQuot_smul_mk π I F k U.1 a y).symm
      naturality := fun {U U'} h => LinearMap.ext fun _ => rfl }
  injective U := Submodule.inclusion_injective
    (idealPowSub_antitone π I F k.le_succ U.1)
  surjective U := (idealPowSuccSub π I F k U.1).mkQ_surjective
  exact U := by
    refine le_antisymm (LinearMap.range_le_ker_iff.mpr (LinearMap.ext fun y => ?_)) fun x hx => ?_
    · show (idealPowSuccSub π I F k U.1).mkQ (Submodule.inclusion
        (idealPowSub_antitone π I F k.le_succ U.1) y) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr y.2
    · have hx' : x ∈ idealPowSuccSub π I F k U.1 :=
        (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.mem_ker.mp hx :
          (idealPowSuccSub π I F k U.1).mkQ x = 0)
      refine ⟨⟨(idealPowSub π I F k U.1).subtype x, hx'⟩, ?_⟩
      show Submodule.inclusion (idealPowSub_antitone π I F k.le_succ U.1) _ = x
      apply Subtype.ext
      show (idealPowSub π I F k U.1).subtype x
        = (idealPowSub π I F k U.1).subtype x
      rfl

theorem idealAnnihilates_idealPowQuot (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ) :
    IdealAnnihilates π I (idealPowQuot π I F k) := by
  intro U a ha x
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U.1).toModule; haveI := F.isScalarTower U.1
  obtain ⟨y, rfl⟩ := (idealPowSES π I F k).surjective U x
  rw [← (idealPowSES π I F k).proj.app_smul U a y]
  show (idealPowSuccSub π I F k U.1).mkQ (a • y) = 0
  refine (Submodule.Quotient.mk_eq_zero _).mpr
    (show a • y ∈ idealPowSuccSub π I F k U.1 from ?_)
  show a • (idealPowSub π I F k U.1).subtype y
    ∈ idealPowSub π I F (k + 1) U.1
  rw [idealPowSub, Submodule.restrictScalars_mem, pow_succ',
    Submodule.mul_smul]
  exact Submodule.smul_mem_smul ((idealSections_eq_ideal I U).symm ▸ ha) y.2

end QuotPMod

section ZeroSES

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

theorem idealPowSub_zero (I : V.IdealSheafData) (F : OModulePresheaf π)
    (U : V.Opens) : idealPowSub π I F 0 U = ⊤ := by
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule; haveI := F.isScalarTower U
  simp [idealPowSub, pow_zero, Submodule.top_smul]

def idealPowZeroSES (I : V.IdealSheafData) (F : OModulePresheaf π) :
    OModulePresheaf.AffSES (OModulePresheaf.zero π) (idealPow π I F 0) F where
  inc := OModulePresheaf.AffHom.zeroFrom _
  proj :=
    { app := fun U => (idealPowSub π I F 0 U.1).subtype
      app_smul := fun _ _ _ => rfl
      naturality := fun {U U'} h => LinearMap.ext fun x => rfl }
  injective _ _ _ _ := Subsingleton.elim _ _
  surjective U x := ⟨⟨x, idealPowSub_zero π I F U.1 ▸ Submodule.mem_top⟩, rfl⟩
  exact U := le_antisymm (fun _ ⟨_, hz⟩ => hz ▸ LinearMap.mem_ker.mpr rfl)
    (fun x hx => ⟨0, Subtype.ext (LinearMap.mem_ker.mp hx).symm⟩)

end ZeroSES

end AlgebraicGeometry.OModulePresheaf

end
