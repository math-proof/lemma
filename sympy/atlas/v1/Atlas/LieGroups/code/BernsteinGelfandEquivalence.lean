/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BernsteinGelfandEquivalence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.HCBimoduleProjectives
import Lemma.Fin.All_Eq.of.All_Eq.All_Eq_RightAction.All_Eq_RightAction.All_Any_Eq_Sum_RightAction
import Lemma.Int.IsInQPlus0
import Lemma.Int.WeightLE.of.BruhatLE
import Lemma.Int.Level1.ne.Top
import Lemma.Int.FGUeaIotaRange
import sympy.atlas.v1.Atlas.LieGroups.code.CategoryO
import sympy.atlas.v1.Atlas.LieGroups.code.CategoryOII
import sympy.atlas.v1.Atlas.LieGroups.code.JantzenFiltration
import sympy.atlas.v1.Atlas.LieGroups.code.DufloJoseph
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Analysis.Complex.Basic

noncomputable section

open TensorProduct

universe u_R u_g u_mod

structure LieModuleObj (R : Type u_R) [CommRing R]
    (g : Type u_g) [LieRing g] [LieAlgebra R g] where
  carrier : Type u_mod
  [instAddCommGroup : AddCommGroup carrier]
  [instModule : Module R carrier]
  [instLieRingModule : LieRingModule g carrier]
  [instLieModule : LieModule R g carrier]

attribute [instance] LieModuleObj.instAddCommGroup LieModuleObj.instModule
  LieModuleObj.instLieRingModule LieModuleObj.instLieModule

variable {R : Type u_R} [CommRing R]
variable {g : Type u_g} [LieRing g] [LieAlgebra R g]

def IsRegularWeight
    {D : TriangularDecomposition R g}
    {rd : PositiveRootData D}
    (wg : WeylGroupData D)
    (cd : RootCorootData rd)
    (lam : D.𝔥 →ₗ[R] R) : Prop :=
  ∀ α ∈ rd.posRoots, cd.corootPairing (lam + wg.ρ) α ≠ 0

structure LieModuleMor
    (R : Type u_R) [CommRing R]
    (g : Type u_g) [LieRing g] [LieAlgebra R g]
    (X Y : LieModuleObj.{u_R, u_g, u_mod} R g) where
  toLinearMap : X.carrier →ₗ[R] Y.carrier
  lie_compat : ∀ (x : g) (m : X.carrier),
    toLinearMap (⁅x, m⁆) = ⁅x, toLinearMap m⁆

structure LieModuleIso
    (R : Type u_R) [CommRing R]
    (g : Type u_g) [LieRing g] [LieAlgebra R g]
    (X Y : LieModuleObj.{u_R, u_g, u_mod} R g) where
  forward : LieModuleMor R g X Y
  backward : LieModuleMor R g Y X
  left_inv : ∀ m : X.carrier,
    backward.toLinearMap (forward.toLinearMap m) = m
  right_inv : ∀ m : Y.carrier,
    forward.toLinearMap (backward.toLinearMap m) = m

structure TlambdaData
    (theta : CenterCharacter R g) where
  applyObj :
    (Y : LieBimodule.{u_R, u_g, u_mod} R g) →
    (hY : IsInHCThetaOne Y theta) →
    LieModuleObj.{u_R, u_g, u_mod} R g
  applyHom :
    {Y₁ Y₂ : LieBimodule.{u_R, u_g, u_mod} R g} →
    {hY₁ : IsInHCThetaOne Y₁ theta} →
    {hY₂ : IsInHCThetaOne Y₂ theta} →
    HCThetaOneHom Y₁ Y₂ theta hY₁ hY₂ →
    LieModuleMor R g (applyObj Y₁ hY₁) (applyObj Y₂ hY₂)
  applyHom_comp :
    {Y₁ Y₂ Y₃ : LieBimodule.{u_R, u_g, u_mod} R g} →
    {hY₁ : IsInHCThetaOne Y₁ theta} →
    {hY₂ : IsInHCThetaOne Y₂ theta} →
    {hY₃ : IsInHCThetaOne Y₃ theta} →
    (g' : HCThetaOneHom Y₂ Y₃ theta hY₂ hY₃) →
    (f : HCThetaOneHom Y₁ Y₂ theta hY₁ hY₂) →
    (comp_gf : HCThetaOneHom Y₁ Y₃ theta hY₁ hY₃) →
    comp_gf.toLinearMap = g'.toLinearMap.comp f.toLinearMap →
    (applyHom comp_gf).toLinearMap = (applyHom g').toLinearMap.comp (applyHom f).toLinearMap
  applyHom_id :
    {Y : LieBimodule.{u_R, u_g, u_mod} R g} →
    {hY : IsInHCThetaOne Y theta} →
    (idY : HCThetaOneHom Y Y theta hY hY) →
    idY.toLinearMap = LinearMap.id →
    (applyHom idY).toLinearMap = LinearMap.id
  applyHom_surjective :
    {Y₁ Y₂ : LieBimodule.{u_R, u_g, u_mod} R g} →
    {hY₁ : IsInHCThetaOne Y₁ theta} →
    {hY₂ : IsInHCThetaOne Y₂ theta} →
    (f : HCThetaOneHom Y₁ Y₂ theta hY₁ hY₂) →
    Function.Surjective f.toLinearMap →
    Function.Surjective (applyHom f).toLinearMap
  applyHom_exact :
    {Y₁ Y₂ Y₃ : LieBimodule.{u_R, u_g, u_mod} R g} →
    {hY₁ : IsInHCThetaOne Y₁ theta} →
    {hY₂ : IsInHCThetaOne Y₂ theta} →
    {hY₃ : IsInHCThetaOne Y₃ theta} →
    (p₁ : HCThetaOneHom Y₁ Y₂ theta hY₁ hY₂) →
    (p₀ : HCThetaOneHom Y₂ Y₃ theta hY₂ hY₃) →
    Function.Exact p₁.toLinearMap p₀.toLinearMap →
    Function.Surjective p₀.toLinearMap →
    Function.Exact (applyHom p₁).toLinearMap (applyHom p₀).toLinearMap
  applyObj_isCategoryO :
    {D : TriangularDecomposition R g} →
    {rd : PositiveRootData D} →
    (Y : LieBimodule.{u_R, u_g, u_mod} R g) →
    (hY : IsInHCThetaOne Y theta) →
    IsCategoryO D rd (applyObj Y hY).carrier

structure HlambdaData
    (theta : CenterCharacter R g) where
  applyObj :
    (X : LieModuleObj.{u_R, u_g, u_mod} R g) →
    LieBimodule.{u_R, u_g, u_mod} R g
  inHCThetaOne :
    (X : LieModuleObj.{u_R, u_g, u_mod} R g) →
    IsInHCThetaOne (applyObj X) theta

structure IsInBlock_LambdaPlusP
    {D : TriangularDecomposition R g}
    (rd : PositiveRootData D)
    (X : LieModuleObj.{u_R, u_g, u_mod} R g)
    (theta : CenterCharacter R g) : Prop where
  inCategoryO : IsCategoryO D rd X.carrier
  existsUEAAction :
    ∃ (ueaAct : UniversalEnvelopingAlgebra R g →ₐ[R] Module.End R X.carrier),
      GeneralizedEigenspaceCenter X.carrier ueaAct theta = ⊤

def IsInO_Lambda
    {D : TriangularDecomposition R g}
    (rd : PositiveRootData D)
    (theta : CenterCharacter R g)
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    (X : LieModuleObj.{u_R, u_g, u_mod} R g) : Prop :=
  IsInBlock_LambdaPlusP rd X theta ∧
  ∃ (P₀ P₁ : LieBimodule.{u_R, u_g, u_mod} R g)
    (hP₀ : IsInHCThetaOne P₀ theta) (hP₁ : IsInHCThetaOne P₁ theta),
    IsProjectiveInHCThetaOne P₀ theta hP₀ ∧
    IsProjectiveInHCThetaOne P₁ theta hP₁ ∧

    ∃ (_f₁ : (Tl.applyObj P₁ hP₁).carrier →ₗ[R] (Tl.applyObj P₀ hP₀).carrier)
      (f₀ : (Tl.applyObj P₀ hP₀).carrier →ₗ[R] X.carrier),
      Function.Surjective f₀

def VermaCarrier (D : TriangularDecomposition R g) (wt : D.𝔥 →ₗ[R] R) : Type u_mod :=
  (verma_module_exists (R := R) (𝔤 := g) D wt).choose

noncomputable instance VermaCarrier.instACG (D : TriangularDecomposition R g)
    (wt : D.𝔥 →ₗ[R] R) : AddCommGroup (VermaCarrier D wt) :=
  (verma_module_exists (R := R) (𝔤 := g) D wt).choose_spec.choose

noncomputable instance VermaCarrier.instMod (D : TriangularDecomposition R g)
    (wt : D.𝔥 →ₗ[R] R) : Module R (VermaCarrier D wt) :=
  (verma_module_exists (R := R) (𝔤 := g) D wt).choose_spec.choose_spec.choose

noncomputable instance VermaCarrier.instLRM (D : TriangularDecomposition R g)
    (wt : D.𝔥 →ₗ[R] R) : LieRingModule g (VermaCarrier D wt) :=
  (verma_module_exists (R := R) (𝔤 := g) D wt).choose_spec.choose_spec.choose_spec.choose

noncomputable instance VermaCarrier.instLM (D : TriangularDecomposition R g)
    (wt : D.𝔥 →ₗ[R] R) : LieModule R g (VermaCarrier D wt) :=
  (verma_module_exists (R := R) (𝔤 := g) D wt).choose_spec.choose_spec.choose_spec.choose_spec.choose

@[reducible] def LieBimodule.instLieRingModuleOfLeftAction
    (Y : LieBimodule.{u_R, u_g, u_mod} R g) : LieRingModule g Y.carrier where
  bracket x m := Y.leftAction (UniversalEnvelopingAlgebra.ι R x) m
  add_lie x y m := by
    show Y.leftAction (UniversalEnvelopingAlgebra.ι R (x + y)) m =
      Y.leftAction (UniversalEnvelopingAlgebra.ι R x) m +
      Y.leftAction (UniversalEnvelopingAlgebra.ι R y) m
    rw [map_add, map_add, LinearMap.add_apply]
  lie_add x m n := by
    show Y.leftAction (UniversalEnvelopingAlgebra.ι R x) (m + n) =
      Y.leftAction (UniversalEnvelopingAlgebra.ι R x) m +
      Y.leftAction (UniversalEnvelopingAlgebra.ι R x) n
    rw [map_add]
  leibniz_lie x y m := by
    show Y.leftAction (UniversalEnvelopingAlgebra.ι R x)
        (Y.leftAction (UniversalEnvelopingAlgebra.ι R y) m) =
      Y.leftAction (UniversalEnvelopingAlgebra.ι R ⁅x, y⁆) m +
      Y.leftAction (UniversalEnvelopingAlgebra.ι R y)
        (Y.leftAction (UniversalEnvelopingAlgebra.ι R x) m)
    rw [LieHom.map_lie, Ring.lie_def, map_sub, LinearMap.sub_apply, map_mul, map_mul]
    show Y.leftAction _ (Y.leftAction _ m) =
      Y.leftAction _ (Y.leftAction _ m) - Y.leftAction _ (Y.leftAction _ m) +
      Y.leftAction _ (Y.leftAction _ m)
    abel

@[reducible] def LieBimodule.instLieModuleOfLeftAction
    (Y : LieBimodule.{u_R, u_g, u_mod} R g) :
    @LieModule R g Y.carrier _ _ _ Y.instAddCommGroup Y.instModule
      Y.instLieRingModuleOfLeftAction :=
  @LieModule.mk R g Y.carrier _ _ _ Y.instAddCommGroup Y.instModule
    Y.instLieRingModuleOfLeftAction
    (fun r x m => by
      change Y.leftAction (UniversalEnvelopingAlgebra.ι R (r • x)) m =
        r • Y.leftAction (UniversalEnvelopingAlgebra.ι R x) m
      rw [map_smul, map_smul, LinearMap.smul_apply])
    (fun r x m => by
      change Y.leftAction (UniversalEnvelopingAlgebra.ι R x) (r • m) =
        r • Y.leftAction (UniversalEnvelopingAlgebra.ι R x) m
      rw [map_smul])

theorem vermaCarrier_central_character
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {D : TriangularDecomposition R g}
    (wg : WeylGroupData D)
    (wt : D.𝔥 →ₗ[R] R)
    (z : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R g)))
    (m : VermaCarrier D wt) :
    (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R g (VermaCarrier D wt)))
      (z : UniversalEnvelopingAlgebra R g) m = (evalHC D wg (wt + wg.ρ)) z • m := by


  have hvm : Nonempty (IsVermaModule D (VermaCarrier D wt) wt) :=
    (verma_module_exists (R := R) (𝔤 := g) D wt).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  obtain ⟨hIsVerma⟩ := hvm
  have hic := vermaHasInfinitesimalCharacter D wg (VermaCarrier D wt) wt hIsVerma

  exact (vermaHasInfinitesimalCharacter D wg (VermaCarrier D wt) wt hIsVerma).center_acts_by_scalar z m

theorem homFinBimodule_vermaCarrier_isHC
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    [Module.Finite R g] {D : TriangularDecomposition R g}
    (wt : D.𝔥 →ₗ[R] R)
    (N : Type u_mod) [AddCommGroup N] [Module R N] [LieRingModule g N] [LieModule R g N] :
    IsHarishChandraBimodule (HomFinBimodule (R := R) (𝔤 := g) (VermaCarrier D wt) N) := by
  constructor

  intro ⟨T, hT⟩


  obtain ⟨S, hfin, hT_mem, hstab⟩ := hT

  have hS_sub_HomFin : ∀ f : VermaCarrier D wt →ₗ[R] N, f ∈ S → f ∈ HomFin (R := R) (𝔤 := g) (VermaCarrier D wt) N := by
    intro f hf
    exact ⟨S, hfin, hf, hstab⟩

  let S' : Submodule R (↥(HomFin (R := R) (𝔤 := g) (VermaCarrier D wt) N)) :=
    S.comap (HomFin (R := R) (𝔤 := g) (VermaCarrier D wt) N).subtype
  refine ⟨S', ?_, ?_, ?_⟩
  ·


    have : Module.Finite R S := hfin


    let e : S' →ₗ[R] S :=
      { toFun := fun ⟨⟨f, hf_homfin⟩, hf_S⟩ => ⟨f, hf_S⟩
        map_add' := fun _ _ => by ext; rfl
        map_smul' := fun _ _ => by ext; rfl }
    have he_inj : Function.Injective e := fun ⟨⟨f₁, _⟩, _⟩ ⟨⟨f₂, _⟩, _⟩ h => by
      have : f₁ = f₂ := Subtype.mk.inj h
      subst this; rfl
    have he_surj : Function.Surjective e := fun ⟨f, hf_S⟩ =>
      ⟨⟨⟨f, hS_sub_HomFin f hf_S⟩, hf_S⟩, rfl⟩
    exact Module.Finite.equiv (LinearEquiv.ofBijective e ⟨he_inj, he_surj⟩).symm
  ·
    show T ∈ S
    exact hT_mem
  ·
    intro x ⟨f, hf_homfin⟩ hf_S'

    show ((HomFinBimodule (R := R) (𝔤 := g) (VermaCarrier D wt) N).adjointAction x ⟨f, hf_homfin⟩).val ∈ S


    rw [homFinBimodule_adjointAction_val (VermaCarrier D wt) N x ⟨f, hf_homfin⟩]
    exact hstab x f hf_S'

theorem homFinBimodule_right_character
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    [Module.Finite R g] {D : TriangularDecomposition R g}
    (wg : WeylGroupData D)
    (wt : D.𝔥 →ₗ[R] R)
    (X : LieModuleObj.{u_R, u_g, u_mod} R g)
    (z : Subalgebra.center R (UniversalEnvelopingAlgebra R g))
    (m : (HomFinBimodule (R := R) (𝔤 := g) (VermaCarrier D wt) X.carrier).carrier) :
    (HomFinBimodule (R := R) (𝔤 := g) (VermaCarrier D wt) X.carrier).rightAction
      (MulOpposite.op (z : UniversalEnvelopingAlgebra R g)) m =
    (evalHC D wg (wt + wg.ρ)) z • m := by


  obtain ⟨T, hT⟩ := m
  simp only [HomFinBimodule]
  ext v


  show (T ∘ₗ (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R g (VermaCarrier D wt))) (↑z)) v =
    (evalHC D wg (wt + wg.ρ)) z • T v
  rw [LinearMap.comp_apply, vermaCarrier_central_character wg wt z v, T.map_smul]

def Hlambda_exists
    [Module.Finite R g]
    {rd : PositiveRootData D}
    (wg : WeylGroupData D)
    (theta : CenterCharacter R g)
    (lam : D.𝔥 →ₗ[R] R)
    (_hdom : IsDominantWeightLE rd wg lam)
    (htheta : theta = evalHC D wg lam) :
    HlambdaData.{u_R, u_g, u_mod} theta where


  applyObj := fun X =>
    HomFinBimodule (R := R) (𝔤 := g) (VermaCarrier D (lam - wg.ρ)) X.carrier


  inHCThetaOne := fun _X =>
    { isHC := homFinBimodule_vermaCarrier_isHC (lam - wg.ρ) _X.carrier
      right_annihilated := fun z m => by


        have h := homFinBimodule_right_character wg (lam - wg.ρ) _X z m


        simp only [sub_add_cancel] at h
        rw [h, htheta] }

abbrev HCThetaOneObj (R : Type u_R) [CommRing R] (g : Type u_g) [LieRing g] [LieAlgebra R g]
    (theta : CenterCharacter R g) :=
  { Y : LieBimodule.{u_R, u_g, u_mod} R g // IsInHCThetaOne Y theta }

def HCThetaOneHomBundled {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    (theta : CenterCharacter R g)
    (A B : HCThetaOneObj.{u_R, u_g, u_mod} R g theta) : Type u_mod :=
  HCThetaOneHom A.1 B.1 theta A.2 B.2

def TlambdaObjBundled {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    (A : HCThetaOneObj.{u_R, u_g, u_mod} R g theta) : LieModuleObj.{u_R, u_g, u_mod} R g :=
  Tl.applyObj A.1 A.2

def TlambdaMapBundled {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    {A B : HCThetaOneObj.{u_R, u_g, u_mod} R g theta}
    (f : HCThetaOneHomBundled theta A B) :
    LieModuleMor R g (TlambdaObjBundled Tl A) (TlambdaObjBundled Tl B) :=
  Tl.applyHom f

def IsProjHCBundled {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    (theta : CenterCharacter R g)
    (A : HCThetaOneObj.{u_R, u_g, u_mod} R g theta) : Prop :=
  IsProjectiveInHCThetaOne A.1 theta A.2

noncomputable def HCThetaOne_comp
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    {A B C : HCThetaOneObj.{u_R, u_g, u_mod} R g theta} :
    HCThetaOneHomBundled theta B C → HCThetaOneHomBundled theta A B →
    HCThetaOneHomBundled theta A C :=
  fun g' f => {
    toLinearMap := g'.toLinearMap.comp f.toLinearMap
    left_compat := fun u m => by
      simp [LinearMap.comp_apply]
      rw [f.left_compat, g'.left_compat]
    right_compat := fun u m => by
      simp [LinearMap.comp_apply]
      rw [f.right_compat, g'.right_compat]
  }

def LieModuleMor_comp
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {X Y Z : LieModuleObj.{u_R, u_g, u_mod} R g}
    (g' : LieModuleMor R g Y Z) (f : LieModuleMor R g X Y) :
    LieModuleMor R g X Z where
  toLinearMap := g'.toLinearMap.comp f.toLinearMap
  lie_compat x m := by
    simp [LinearMap.comp_apply]
    rw [f.lie_compat, g'.lie_compat]

def LieModuleMor_sub
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {X Y : LieModuleObj.{u_R, u_g, u_mod} R g}
    (f g' : LieModuleMor R g X Y) : LieModuleMor R g X Y where
  toLinearMap := f.toLinearMap - g'.toLinearMap
  lie_compat x m := by
    simp only [LinearMap.sub_apply]
    rw [f.lie_compat, g'.lie_compat, lie_sub]

noncomputable def HCThetaOne_id
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    (A : HCThetaOneObj.{u_R, u_g, u_mod} R g theta) :
    HCThetaOneHomBundled theta A A :=
  { toLinearMap := LinearMap.id
    left_compat := fun _ _ => rfl
    right_compat := fun _ _ => rfl }

def LieModuleMor_id
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    (X : LieModuleObj.{u_R, u_g, u_mod} R g) :
    LieModuleMor R g X X where
  toLinearMap := LinearMap.id
  lie_compat _ _ := rfl

def IsPresentationHC
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    {P₁ P₀ X : HCThetaOneObj.{u_R, u_g, u_mod} R g theta}
    (p₁ : HCThetaOneHomBundled theta P₁ P₀) (p₀ : HCThetaOneHomBundled theta P₀ X) : Prop :=
  Function.Surjective p₀.toLinearMap ∧
  (∀ m : P₁.1.carrier, p₀.toLinearMap (p₁.toLinearMap m) = 0) ∧
  (∀ m : P₀.1.carrier, p₀.toLinearMap m = 0 → ∃ n : P₁.1.carrier, p₁.toLinearMap n = m)

def IsPresentationO
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {Q₁ Q₀ Y : LieModuleObj.{u_R, u_g, u_mod} R g}
    (q₁ : LieModuleMor R g Q₁ Q₀) (q₀ : LieModuleMor R g Q₀ Y) : Prop :=
  Function.Surjective q₀.toLinearMap ∧
  (∀ m : Q₁.carrier, q₀.toLinearMap (q₁.toLinearMap m) = 0) ∧
  (∀ m : Q₀.carrier, q₀.toLinearMap m = 0 → ∃ n : Q₁.carrier, q₁.toLinearMap n = m)

def IsProjO
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    (P : LieModuleObj.{u_R, u_g, u_mod} R g) : Prop :=
  ∀ (Y₁ Y₂ : LieModuleObj.{u_R, u_g, u_mod} R g)
    (g' : LieModuleMor R g Y₁ Y₂) (f : LieModuleMor R g P Y₂),
    Function.Surjective g'.toLinearMap →
    ∃ (f' : LieModuleMor R g P Y₁),
      ∀ m : P.carrier, g'.toLinearMap (f'.toLinearMap m) = f.toLinearMap m

def IsIsoO
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {Y₁ Y₂ : LieModuleObj.{u_R, u_g, u_mod} R g}
    (f : LieModuleMor R g Y₁ Y₂) : Prop :=
  ∃ (g' : LieModuleMor R g Y₂ Y₁),
    (∀ m : Y₁.carrier, g'.toLinearMap (f.toLinearMap m) = m) ∧
    (∀ m : Y₂.carrier, f.toLinearMap (g'.toLinearMap m) = m)

noncomputable instance LieModuleMor_ker_lieRingModule
    {X Y : LieModuleObj.{u_R, u_g, u_mod} R g}
    (f : LieModuleMor R g X Y) : LieRingModule g f.toLinearMap.ker where
  bracket x m := ⟨⁅x, m.1⁆, by
    simp [LinearMap.mem_ker]; rw [f.lie_compat, m.2, lie_zero]⟩
  add_lie x y m := Subtype.ext (add_lie x y m.1)
  lie_add x m n := Subtype.ext (lie_add x m.1 n.1)
  leibniz_lie x y m := Subtype.ext (leibniz_lie x y m.1)

noncomputable instance LieModuleMor_ker_lieModule
    {X Y : LieModuleObj.{u_R, u_g, u_mod} R g}
    (f : LieModuleMor R g X Y) : LieModule R g f.toLinearMap.ker where
  smul_lie r x m := by
    apply Subtype.ext; show ⁅r • x, m.1⁆ = r • ⁅x, m.1⁆; exact smul_lie r x m.1
  lie_smul r x m := by
    apply Subtype.ext; show ⁅x, r • m.1⁆ = r • ⁅x, m.1⁆; exact lie_smul r x m.1

noncomputable def LieModuleMor_kerObj
    {X Y : LieModuleObj.{u_R, u_g, u_mod} R g}
    (f : LieModuleMor R g X Y) : LieModuleObj.{u_R, u_g, u_mod} R g where
  carrier := f.toLinearMap.ker

noncomputable def LieModuleMor_corestrToKer
    {A B C : LieModuleObj.{u_R, u_g, u_mod} R g}
    (q₁ : LieModuleMor R g A B) (q₀ : LieModuleMor R g B C)
    (hcomp : ∀ m : A.carrier, q₀.toLinearMap (q₁.toLinearMap m) = 0) :
    LieModuleMor R g A (LieModuleMor_kerObj q₀) where
  toLinearMap := q₁.toLinearMap.codRestrict q₀.toLinearMap.ker (fun m => by
    simp [LinearMap.mem_ker]; exact hcomp m)
  lie_compat x m := by
    apply Subtype.ext
    show q₁.toLinearMap ⁅x, m⁆ = ⁅x, q₁.toLinearMap m⁆
    exact q₁.lie_compat x m

def IsKFiniteVector
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module R V]
    (π : Representation R G V) (K : Subgroup G) (v : V) : Prop :=
  (Submodule.span R (Set.range (fun k : K => π k v))).FG

def IsAdmissibleRepresentation
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module R V]
    (π : Representation R G V) (K : Subgroup G) : Prop :=
  ∀ v : V, IsKFiniteVector π K v →
    ∃ (S : Submodule R V), Module.Finite R S ∧ v ∈ S ∧
      ∀ (k : K) (s : V), s ∈ S → π (k : G) s ∈ S

structure RealizingRepData
    (theta : CenterCharacter R g)
    (M : LieBimodule.{u_R, u_g, u_mod} R g)
    (_hM : IsInHCThetaOne M theta) where
  G : Type*
  [instGroupG : Group G]
  [instTopG : TopologicalSpace G]
  [instTopGroupG : IsTopologicalGroup G]
  [instSCG : SimplyConnectedSpace G]
  K : Subgroup G
  [instCompactK : CompactSpace K]
  V : Type*
  [instNACGV : NormedAddCommGroup V]
  [instIPSV : InnerProductSpace ℂ V]
  [instCompleteV : CompleteSpace V]
  [instModRV : Module R V]
  [instLieRingModuleGV : LieRingModule g V]
  [instLieModuleGV : LieModule R g V]
  π : Representation R G V
  admissible : IsAdmissibleRepresentation π K
  kFinBimod : LieBimodule.{u_R, u_g, u_mod} R g
  kFinInHCTheta : IsInHCThetaOne kFinBimod theta
  embedding : kFinBimod.carrier →ₗ[R] V
  embedding_injective : Function.Injective embedding
  embedding_lie_compat : ∀ (x : g) (w : kFinBimod.carrier),
    embedding (kFinBimod.leftAction (UniversalEnvelopingAlgebra.ι R x) w) =
    instLieRingModuleGV.bracket x (embedding w)
  embedding_KFinite : ∀ w : kFinBimod.carrier, IsKFiniteVector π K (embedding w)
  isoForward : HCThetaOneHom kFinBimod M theta kFinInHCTheta _hM
  isoBackward : HCThetaOneHom M kFinBimod theta _hM kFinInHCTheta
  iso_left_inv : ∀ m : M.carrier,
    isoForward.toLinearMap (isoBackward.toLinearMap m) = m
  iso_right_inv : ∀ v : kFinBimod.carrier,
    isoBackward.toLinearMap (isoForward.toLinearMap v) = v

attribute [instance] RealizingRepData.instGroupG RealizingRepData.instTopG
  RealizingRepData.instTopGroupG RealizingRepData.instSCG
  RealizingRepData.instCompactK RealizingRepData.instNACGV
  RealizingRepData.instIPSV RealizingRepData.instCompleteV
  RealizingRepData.instModRV RealizingRepData.instLieRingModuleGV
  RealizingRepData.instLieModuleGV

universe u_G u_V
