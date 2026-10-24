/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DModulesII.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Support
import sympy.atlas.v1.Atlas.LieGroups.code.DModuleApplications
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Abelian
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Topology.Irreducible
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

open CategoryTheory

namespace DModulesII


def IsSupportedOn {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (I : Ideal R) : Prop :=
  ∀ (f : R), f ∈ I → ∀ (v : M), ∃ N : ℕ, (f ^ N) • v = 0

def sheafSupport (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    Set (PrimeSpectrum R) :=
  ⋂ (I : Ideal R) (_ : IsSupportedOn M I), PrimeSpectrum.zeroLocus (I : Set R)

section DModules

variable {R : Type*} [CommRing R] {D : Type*} [Ring D] (ι : R →+* D)

@[reducible]
def rModuleOf (M : Type*) [AddCommGroup M] [Module D M] : Module R M :=
  Module.compHom M ι

def DModIsSupportedOn (M : Type*) [AddCommGroup M] [Module D M] (I : Ideal R) : Prop :=
  @IsSupportedOn R _ M _ (rModuleOf ι M) I

abbrev DModSupportedPred (I : Ideal R) : ObjectProperty (ModuleCat D) := fun M =>
  ∀ (f : R), f ∈ I → ∀ (v : M), ∃ N : ℕ, (ι f ^ N) • v = 0

abbrev DModSupportedCat (I : Ideal R) := (DModSupportedPred ι I).FullSubcategory

def annihilatedByIdeal (I : Ideal R) (M : Type*) [AddCommGroup M] [Module D M] : Set M :=
  {v : M | ∀ f ∈ I, (ι f) • v = 0}

def annihilatedByIdealAddSubgroup (I : Ideal R) (M : Type*) [AddCommGroup M] [Module D M] :
    AddSubgroup M where
  carrier := annihilatedByIdeal ι I M
  zero_mem' := fun f _ => smul_zero _
  add_mem' := fun {a b} ha hb f hf => by
    show (ι f) • (a + b) = 0
    rw [smul_add, ha f hf, hb f hf, add_zero]
  neg_mem' := fun {a} ha f hf => by
    show (ι f) • (-a) = 0
    rw [smul_neg, ha f hf, neg_zero]

def DModSheafSupport (M : Type*) [AddCommGroup M] [Module D M] : Set (PrimeSpectrum R) :=
  @sheafSupport R _ M _ (rModuleOf ι M)

class IsLeibnizCompatible (ι : R →+* D) (M : Type*) [AddCommGroup M] [Module D M] : Prop where
  smul_torsion : ∀ (d : D) (f : R) (m : M) (n : ℕ),
    (ι f ^ n) • m = 0 → ∃ N : ℕ, (ι f ^ N) • (d • m) = 0

class IsKashiwaraSetup
    {R : Type*} [CommRing R] {D : Type*} [Ring D] (_ : R →+* D)
    (I : Ideal R) (D' : Type*) [Ring D'] (ι' : R ⧸ I →+* D') : Prop where
  isSmooth_X : IsNoetherian R R
  isSmooth_Z : IsNoetherian (R ⧸ I) (R ⧸ I)
  ι'_injective : Function.Injective ι'

end DModules


section GEquivariantSheafDef

universe u_sheaf

structure QCohSheafData (k : Type u_sheaf) [Field k] where
  affineIndex : Type u_sheaf
  coordRing : affineIndex → Type u_sheaf
  [instCommRing : ∀ i, CommRing (coordRing i)]
  [instAlgebra : ∀ i, Algebra k (coordRing i)]
  diffOpsRing : affineIndex → Type u_sheaf
  [instDiffRing : ∀ i, Ring (diffOpsRing i)]
  sections : affineIndex → Type u_sheaf
  [instAddCommGroup : ∀ i, AddCommGroup (sections i)]
  [instModule : ∀ i, Module (diffOpsRing i) (sections i)]
  [instModuleK : ∀ i, Module k (sections i)]

attribute [instance] QCohSheafData.instCommRing QCohSheafData.instAlgebra
  QCohSheafData.instDiffRing QCohSheafData.instAddCommGroup QCohSheafData.instModule
  QCohSheafData.instModuleK

structure GEquivariantSheaf (k : Type u_sheaf) [Field k]
    (G : Type u_sheaf) [Group G] where
  sheafData : QCohSheafData k
  [mulAction : MulAction G sheafData.affineIndex]
  phi : (g : G) → (i : sheafData.affineIndex) →
    sheafData.sections i ≃ₗ[k] sheafData.sections (g • i)
  cocycle : ∀ (g h : G) (i : sheafData.affineIndex) (v : sheafData.sections i),
    (mul_smul g h i) ▸ (phi (g * h) i v) =
    phi g (h • i) (phi h i v)
  phi_one : ∀ (i : sheafData.affineIndex) (v : sheafData.sections i),
    (one_smul G i) ▸ (phi 1 i v) = v

end GEquivariantSheafDef


section Equivariant

variable (k : Type*) [Field k]
         (G : Type*) [Group G]
         (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra k 𝔤]
         (D : Type*) [Ring D] [Algebra k D]

structure GEquivQCohSheaf
    (M : Type*) [AddCommGroup M] [Module k M] where
  groupAction : G →* (M ≃ₗ[k] M)

structure WeaklyEquivDModule
    (M : Type*) [AddCommGroup M] [Module k M] [Module D M]
    extends GEquivQCohSheaf k G M where
  groupAction_DLinear : ∀ (g : G) (d : D) (m : M),
    groupAction g (d • m) = d • (groupAction g m)

structure EquivDModule
    (M : Type*) [AddCommGroup M] [Module k M] [Module D M]
    extends WeaklyEquivDModule k G D M where
  lieToD : 𝔤 →ₗ⁅k⁆ D
  lieAction_phi : 𝔤 →ₗ[k] Module.End k M
  actions_agree : ∀ (x : 𝔤) (v : M), lieAction_phi x v = (lieToD x) • v

def rho_phi {M : Type*} [AddCommGroup M] [Module k M] [Module D M]
    (_W : WeaklyEquivDModule k G D M)
    (lieAction_phi : 𝔤 →ₗ[k] Module.End k M)
    (lieToD : 𝔤 →ₗ⁅k⁆ D) (x : 𝔤) (v : M) : M :=
  lieAction_phi x v - (lieToD x) • v

abbrev MonodromicDModule
    (T : Type*) [CommGroup T]
    (D' : Type*) [Ring D'] [Algebra k D']
    (M : Type*) [AddCommGroup M] [Module k M] [Module D' M] :=
  WeaklyEquivDModule k T D' M

def monodromic_rho_phi
    {M : Type*} [AddCommGroup M] [Module k M] [Module D M]
    (W : WeaklyEquivDModule k G D M)
    (lieAction_phi : 𝔤 →ₗ[k] Module.End k M)
    (lieToD : 𝔤 →ₗ⁅k⁆ D) (x : 𝔤) (v : M) : M :=
  rho_phi k G 𝔤 D W lieAction_phi lieToD x v

end Equivariant


section DAffine

universe u_dxmod u_aag

variable (k : Type u_aag) [Field k]
         (K : Type u_aag) [Group K]
         (𝔨 : Type u_aag) [LieRing 𝔨] [LieAlgebra k 𝔨]
         (D : Type u_aag) [Ring D] [Algebra k D]

class IsDaffine (DXMod : Type*) [Category.{u_dxmod} DXMod] (X : Type*) : Prop where
  isNoetherian_DX : IsNoetherian D D
  globalSections_equiv : Nonempty (DXMod ≌ ModuleCat.{u_dxmod} D)

structure IsAffineAlgebraicGroup (G : Type u_aag) [Group G] : Prop where
  fg : Group.FG G

class IsAntidominant {k' : Type*} [Field k'] (𝔥star : Type*)
    (posRoots : Set 𝔥star) (pairing : 𝔥star → 𝔥star → k') (lam : 𝔥star) : Prop where
  not_pos_int_pairing : ∀ α ∈ posRoots, ¬(∃ n : ℕ, n > 0 ∧ pairing lam α = (n : k'))

def StrongKEquivDModPred (lieToD : 𝔨 →ₗ⁅k⁆ D) : ObjectProperty (ModuleCat.{u_aag} D) := fun M => by
  letI : Module k M := Module.compHom M (algebraMap k D)
  exact ∃ (groupAct : K →* (M ≃ₗ[k] M))
    (_ : ∀ (g : K) (d : D) (m : M), groupAct g (d • m) = d • (groupAct g m))
    (liePhi : 𝔨 →ₗ[k] Module.End k M)
    (_ : ∀ (x y : 𝔨), liePhi ⁅x, y⁆ = liePhi x * liePhi y - liePhi y * liePhi x),
    ∀ (x : 𝔨) (v : M), liePhi x v = (lieToD x) • v

def CompatibleKActionPred (lieToD : 𝔨 →ₗ⁅k⁆ D) (Ad : K →* (𝔨 ≃ₗ[k] 𝔨)) :
    ObjectProperty (ModuleCat.{u_aag} D) := fun M => by
  letI : Module k M := Module.compHom M (algebraMap k D)
  exact ∃ (groupAct : K →* (M ≃ₗ[k] M))
    (_ : ∀ (m : M), (Submodule.span k (Set.range (fun g => (groupAct g : M ≃ₗ[k] M) m))).FG)
    (lieAct : 𝔨 →ₗ[k] Module.End k M),

    (∀ (x : 𝔨) (v : M), lieAct x v = (lieToD x) • v) ∧


    (∀ (g : K) (x : 𝔨) (v : M),
      (groupAct g) ((lieAct x) ((groupAct g).symm v)) = (lieAct (Ad g x)) v)

structure BBLocalizationData (k' : Type u_aag) [Field k'] where
  G : Type u_aag
  [grpG : Group G]
  K : Type u_aag
  [grpK : Group K]
  iK : K →* G
  𝔤 : Type u_aag
  [lieRing_𝔤 : LieRing 𝔤]
  [lieAlg_𝔤 : LieAlgebra k' 𝔤]
  𝔨 : Type u_aag
  [lieRing_𝔨 : LieRing 𝔨]
  [lieAlg_𝔨 : LieAlgebra k' 𝔨]
  ι𝔨 : 𝔨 →ₗ⁅k'⁆ 𝔤
  𝔥 : Type u_aag
  [lieRing_𝔥 : LieRing 𝔥]
  [lieAlg_𝔥 : LieAlgebra k' 𝔥]
  ι𝔥 : 𝔥 →ₗ⁅k'⁆ 𝔤
  D : Type u_aag
  [ring_D : Ring D]
  [alg_D : Algebra k' D]
  lieToD : 𝔤 →ₗ⁅k'⁆ D
  𝔥star : Type u_aag
  [add_𝔥star : AddCommGroup 𝔥star]
  [mod_𝔥star : Module k' 𝔥star]
  duality : 𝔥 →ₗ[k'] 𝔥star →ₗ[k'] k'
  roots : Set 𝔥star
  posRoots : Set 𝔥star
  lam : 𝔥star
  FlagVariety : Type u_aag
  [isNoetherian_D : IsNoetherian D D]
  aag_K : IsAffineAlgebraicGroup K
  Ad_K : K →* (𝔨 ≃ₗ[k'] 𝔨)

attribute [instance] BBLocalizationData.grpG BBLocalizationData.grpK
  BBLocalizationData.lieRing_𝔤 BBLocalizationData.lieAlg_𝔤
  BBLocalizationData.lieRing_𝔨 BBLocalizationData.lieAlg_𝔨
  BBLocalizationData.lieRing_𝔥 BBLocalizationData.lieAlg_𝔥
  BBLocalizationData.ring_D BBLocalizationData.alg_D
  BBLocalizationData.add_𝔥star BBLocalizationData.mod_𝔥star
  BBLocalizationData.isNoetherian_D

def BBLocalizationData.IsAntidominant {k' : Type u_aag} [Field k']
    (bd : BBLocalizationData k') : Prop :=
  ∀ α ∈ bd.posRoots, ∀ hv : bd.𝔥, ¬(∃ n : ℕ, n > 0 ∧ (bd.duality hv) (bd.lam - n • α) = 0)

def IsKEquivDModBB {k' : Type u_aag} [Field k']
    (bd : BBLocalizationData k') : ObjectProperty (ModuleCat.{u_aag} bd.D) := fun M =>
  let _instk : Module k' M := Module.compHom M (algebraMap k' bd.D)
  ∃ (groupAction : bd.K →* (M ≃ₗ[k'] M)),
    (∀ (g : bd.K) (d : bd.D) (m : M), groupAction g (d • m) = d • (groupAction g m)) ∧
    ∃ (lieAction : bd.𝔨 →ₗ[k'] Module.End k' M),
      (∀ (x y : bd.𝔨), lieAction ⁅x, y⁆ =
        lieAction x * lieAction y - lieAction y * lieAction x) ∧
      (∀ (x : bd.𝔨) (v : M), lieAction x v = (bd.lieToD (bd.ι𝔨 x)) • v)

def IsGKModBB {k' : Type u_aag} [Field k']
    (bd : BBLocalizationData k') : ObjectProperty (ModuleCat.{u_aag} bd.D) := fun M => by
  letI : Module k' M := Module.compHom M (algebraMap k' bd.D)
  exact ∃ (groupAct : bd.K →* (M ≃ₗ[k'] M))
    (_ : ∀ (m : M), (Submodule.span k' (Set.range (fun g => (groupAct g : M ≃ₗ[k'] M) m))).FG)
    (lieAct : bd.𝔨 →ₗ[k'] Module.End k' M),

    (∀ (x : bd.𝔨) (v : M), lieAct x v = (bd.lieToD (bd.ι𝔨 x)) • v) ∧

    (∀ (g : bd.K) (x : bd.𝔨) (v : M),
      (groupAct g) ((lieAct x) ((groupAct g).symm v)) = (lieAct (bd.Ad_K g x)) v)
