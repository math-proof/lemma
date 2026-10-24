/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/TranslationFunctors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.CategoryOII
import Lemma.Int.WeightLE.of.BruhatLE
import Lemma.Int.FGUeaIotaRange
import Lemma.Int.All_Eq_0.of.EqCompositionLengthO_0.IsCategoryO
import Lemma.Int.IsCategoryOA.of.IsCategoryOB
import sympy.atlas.v1.Atlas.LieGroups.code.DufloJoseph
import sympy.atlas.v1.Atlas.LieGroups.code.BGGReciprocity
import sympy.atlas.v1.Atlas.LieGroups.code.TensorO
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.Algebra.Lie.Semisimple.Basic

noncomputable section

open scoped TensorProduct

universe uM

variable {R : Type*} [CommRing R]
variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
variable (Δ : TriangularDecomposition R 𝔤)
variable (rd : PositiveRootData Δ)
variable (wg : WeylGroupData Δ)

local notation "𝔥*" => (Δ.𝔥 →ₗ[R] R)

structure TranslationFunctorData where
  lam : 𝔥*
  mu : 𝔥*
  V : Type*
  [V_addCommGroup : AddCommGroup V]
  [V_module : Module R V]
  [V_lieRingModule : LieRingModule 𝔤 V]
  [V_lieModule : LieModule R 𝔤 V]
  [V_finiteDim : Module.Finite R V]
  [V_irreducible : IsSimpleModule R V]
  lam_dominant : IsDominantWeightLE rd wg lam
  mu_dominant : IsDominantWeightLE rd wg mu
  extremal_weight : mu - lam ∈ weights Δ V

attribute [instance] TranslationFunctorData.V_addCommGroup
  TranslationFunctorData.V_module TranslationFunctorData.V_lieRingModule
  TranslationFunctorData.V_lieModule TranslationFunctorData.V_finiteDim
  TranslationFunctorData.V_irreducible

structure TranslationFunctorData.ApplyResult
    (F : TranslationFunctorData Δ rd wg)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] where
  carrier : Type*
  [instAddCommGroup : AddCommGroup carrier]
  [instModule : Module R carrier]
  [instLieRingModule : LieRingModule 𝔤 carrier]
  [instLieModule : LieModule R 𝔤 carrier]
  hasInfChar : HasInfinitesimalCharacter (R := R) (𝔤 := 𝔤) carrier (evalHC Δ wg F.mu)

attribute [instance] TranslationFunctorData.ApplyResult.instAddCommGroup
  TranslationFunctorData.ApplyResult.instModule
  TranslationFunctorData.ApplyResult.instLieRingModule
  TranslationFunctorData.ApplyResult.instLieModule

section CharEigenspace

variable {R : Type*} [CommRing R]
variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
variable (act : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
variable (χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R)

def charEigenspace : Submodule R M where
  carrier := {m : M | ∀ z : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)),
    act (z : UniversalEnvelopingAlgebra R 𝔤) m = χ z • m}
  zero_mem' z := by simp [map_zero, smul_zero]
  add_mem' {a b} ha hb z := by simp [map_add, ha z, hb z, smul_add]
  smul_mem' r m hm z := by
    show act (↑z) (r • m) = χ z • (r • m)
    rw [(act (↑z)).map_smul, hm z, smul_comm]

set_option linter.unusedSectionVars false in
theorem charEigenspace_closed_uea (u : UniversalEnvelopingAlgebra R 𝔤) {m : M}
    (hm : m ∈ charEigenspace act χ) :
    act u m ∈ charEigenspace act χ := by
  intro z

  have h1 : (act (↑z)) ((act u) m) =
      (act ((↑z : UniversalEnvelopingAlgebra R 𝔤) * u)) m := by
    rw [map_mul]; rfl

  have hc : (z : UniversalEnvelopingAlgebra R 𝔤) * u =
      u * (z : UniversalEnvelopingAlgebra R 𝔤) :=
    ((Subalgebra.mem_center_iff.mp z.property) u).symm

  have h2 : (act (u * (↑z : UniversalEnvelopingAlgebra R 𝔤))) m =
      (act u) ((act (↑z)) m) := by
    rw [map_mul]; rfl
  rw [h1, hc, h2, hm z, (act u).map_smul]

def charEigenspaceLie
    (hcompat : ∀ (x : 𝔤) (m : M),
      act (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆) :
    LieSubmodule R 𝔤 M where
  __ := charEigenspace act χ
  lie_mem {x m} hm := by
    show ⁅x, m⁆ ∈ charEigenspace act χ
    rw [← hcompat x m]
    exact charEigenspace_closed_uea act χ (UniversalEnvelopingAlgebra.ι R x) hm

noncomputable def restrictedUEAAction
    (hcompat : ∀ (x : 𝔤) (m : M),
      act (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆) :
    UniversalEnvelopingAlgebra R 𝔤 →ₐ[R]
      Module.End R ↥(charEigenspaceLie act χ hcompat) where
  toFun u :=
    { toFun := fun ⟨m, hm⟩ =>
        ⟨act u m, charEigenspace_closed_uea act χ u hm⟩
      map_add' := fun ⟨a, _⟩ ⟨b, _⟩ => by simp [Subtype.ext_iff, map_add]
      map_smul' := fun r ⟨m, _⟩ => by simp [Subtype.ext_iff, (act u).map_smul] }
  map_one' := by ext ⟨m, _⟩; simp [map_one]
  map_mul' a b := by
    ext ⟨m, _⟩
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply]
    show (act (a * b) m : M) = act a (act b m)
    rw [map_mul]; rfl
  map_zero' := by ext ⟨m, _⟩; simp [map_zero]
  map_add' a b := by
    ext ⟨m, _⟩; simp [map_add, LinearMap.add_apply]
  commutes' r := by
    ext ⟨m, _⟩
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    show (act (algebraMap R _ r) m : M) = r • m
    rw [AlgHom.commutes]; rfl

theorem restrictedUEAAction_compat
    (hcompat : ∀ (x : 𝔤) (m : M),
      act (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (x : 𝔤) (m : ↥(charEigenspaceLie act χ hcompat)) :
    restrictedUEAAction act χ hcompat (UniversalEnvelopingAlgebra.ι R x) m =
      ⁅x, m⁆ := by
  ext; simp [restrictedUEAAction]; exact hcompat x ↑m

theorem restrictedUEA_center_acts
    (hcompat : ∀ (x : 𝔤) (m : M),
      act (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (z : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)))
    (m : ↥(charEigenspaceLie act χ hcompat)) :
    restrictedUEAAction act χ hcompat
      (z : UniversalEnvelopingAlgebra R 𝔤) m = χ z • m := by
  ext; simp [restrictedUEAAction]; exact m.property z

end CharEigenspace

noncomputable def TranslationFunctorData.applyToModule
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (F : TranslationFunctorData Δ rd wg)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] :
    F.ApplyResult Δ rd wg M :=
  let act := ueaActionFromLieModule (R := R) (𝔤 := 𝔤) (F.V ⊗[R] M)
  let hcompat := ueaActionFromLieModule_compat (R := R) (𝔤 := 𝔤) (F.V ⊗[R] M)
  let χ := evalHC Δ wg F.mu
  let S := charEigenspaceLie act χ hcompat
  { carrier := ↥S
    instAddCommGroup := inferInstance
    instModule := inferInstance
    instLieRingModule := inferInstance
    instLieModule := inferInstance
    hasInfChar :=
      { ueaAction := restrictedUEAAction act χ hcompat
        compat := restrictedUEAAction_compat act χ hcompat
        center_acts_by_scalar := restrictedUEA_center_acts act χ hcompat } }

structure IsContragredientLieModule
    (V : Type*) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (W : Type*) [AddCommGroup W] [Module R W]
    [LieRingModule 𝔤 W] [LieModule R 𝔤 W] where
  pairing : V →ₗ[R] W →ₗ[R] R
  nondegenerate_left : ∀ v : V, (∀ w : W, pairing v w = 0) → v = 0
  nondegenerate_right : ∀ w : W, (∀ v : V, pairing v w = 0) → w = 0
  equivariant : ∀ (x : 𝔤) (v : V) (w : W),
    pairing (⁅x, v⁆) w + pairing v (⁅x, w⁆) = 0

def IsContragredientLieModule.symm
    {V : Type*} [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    {W : Type*} [AddCommGroup W] [Module R W] [LieRingModule 𝔤 W] [LieModule R 𝔤 W]
    (h : IsContragredientLieModule (R := R) (𝔤 := 𝔤) V W) :
    IsContragredientLieModule (R := R) (𝔤 := 𝔤) W V where
  pairing :=
    { toFun := fun w =>
        { toFun := fun v => h.pairing v w
          map_add' := fun v₁ v₂ => by simp [map_add]
          map_smul' := fun r v => by simp [map_smul] }
      map_add' := fun w₁ w₂ => by
        ext v; simp [map_add]
      map_smul' := fun r w => by
        ext v; simp [map_smul] }
  nondegenerate_left := fun w hw => h.nondegenerate_right w (fun v => hw v)
  nondegenerate_right := fun v hv => h.nondegenerate_left v (fun w => hv w)
  equivariant := fun x w v => by
    have h_eq := h.equivariant x v w


    rw [add_comm]
    exact h_eq

def TwoSidedIdeal.toSubmoduleR {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (J : TwoSidedIdeal A) : Submodule R A where
  carrier := (J : Set A)
  add_mem' ha hb := J.add_mem ha hb
  zero_mem' := J.zero_mem
  smul_mem' r a ha := by rw [Algebra.smul_def]; exact J.mul_mem_left _ _ ha

noncomputable def idealToSubmoduleEvalAtV {R A M : Type*} [CommRing R] [Ring A] [Algebra R A]
    [AddCommGroup M] [Module R M] (act : A →ₐ[R] Module.End R M) (v : M) : A →ₗ[R] M where
  toFun u := act u v
  map_add' x y := by simp [map_add, LinearMap.add_apply]
  map_smul' r x := by
    simp only [RingHom.id_apply]
    show act (r • x) v = r • (act x v)
    rw [Algebra.smul_def, map_mul]
    simp [AlgHom.commutes]
