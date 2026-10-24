/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BorelWeil.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Rank
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.Algebra.Lie.Weights.Killing
import Mathlib.Algebra.Lie.Weights.RootSystem

noncomputable section

universe u v

structure BorelWeilData where
  (k : Type u)
  [field_k : Field k]
  (𝔤 : Type v)
  [lieRing : LieRing 𝔤]
  [lieAlgebra : LieAlgebra k 𝔤]
  (G : Type*)
  [group_G : Group G]
  (WeightLattice : Type*)
  [wl_addCommGroup : AddCommGroup WeightLattice]
  (IsDominant : WeightLattice → Prop)
  (IrrepModule : WeightLattice → Type*)
  [irrepAddCommGroup : ∀ w, AddCommGroup (IrrepModule w)]
  [irrepModule : ∀ w, Module k (IrrepModule w)]
  [irrepFinDim : ∀ w, Module.Finite k (IrrepModule w)]
  (irrepRep : ∀ w, Representation k G (IrrepModule w))

  (FlagVar : Type*)
  (GlobalSections : WeightLattice → Type*)
  [sectionsAddCommGroup : ∀ w, AddCommGroup (GlobalSections w)]
  [sectionsModule : ∀ w, Module k (GlobalSections w)]
  (sectionsRep : ∀ w, Representation k G (GlobalSections w))

attribute [instance] BorelWeilData.field_k BorelWeilData.lieRing BorelWeilData.lieAlgebra
  BorelWeilData.group_G BorelWeilData.wl_addCommGroup BorelWeilData.irrepAddCommGroup
  BorelWeilData.irrepModule BorelWeilData.irrepFinDim BorelWeilData.sectionsAddCommGroup
  BorelWeilData.sectionsModule

structure ParabolicBorelWeilData extends BorelWeilData where
  (SimpleRoots : Type*)
  (S : Set SimpleRoots)
  (coroot_pairing : WeightLattice → SimpleRoots → ℤ)
  (PartialFlagVar : Type*)
  (projection : FlagVar → PartialFlagVar)
  (PartialFlagSections : WeightLattice → Type*)
  [pfSectionsAddCommGroup : ∀ w, AddCommGroup (PartialFlagSections w)]
  [pfSectionsModule : ∀ w, Module k (PartialFlagSections w)]
  (pfSectionsRep : ∀ w, Representation k G (PartialFlagSections w))

attribute [instance] ParabolicBorelWeilData.pfSectionsAddCommGroup
  ParabolicBorelWeilData.pfSectionsModule

def ParabolicBorelWeilData.IsOrthogonalToS (D : ParabolicBorelWeilData)
    (μ : D.WeightLattice) : Prop :=
  ∀ i : D.SimpleRoots, i ∈ D.S → D.coroot_pairing μ i = 0

def nilpotentCone (k : Type*) (𝔤 : Type*) [CommRing k] [LieRing 𝔤] [LieAlgebra k 𝔤] :
    Set 𝔤 :=
  {x : 𝔤 | IsNilpotent (LieAlgebra.ad k 𝔤 x)}

structure SpringerResolutionData where
  (k : Type u)
  [field_k : Field k]
  (𝔤 : Type v)
  [lieRing : LieRing 𝔤]
  [lieAlgebra : LieAlgebra k 𝔤]
  (FlagVar : Type*)
  (CotangentBundle : Type*)
  (springerMap : CotangentBundle → 𝔤)
  (springerMap_mem_nilpotentCone :
    ∀ y : CotangentBundle, springerMap y ∈ nilpotentCone k 𝔤)
  (bundleProjection : CotangentBundle → FlagVar)
  (cotangentBundle_ext : ∀ y₁ y₂ : CotangentBundle,
    bundleProjection y₁ = bundleProjection y₂ →
    springerMap y₁ = springerMap y₂ → y₁ = y₂)
  (IsRegularNilpotent : 𝔤 → Prop)
  (regularNilpotent_mem : ∀ e, IsRegularNilpotent e → e ∈ nilpotentCone k 𝔤)
  (regularNilpotent_nonempty : ∃ e, IsRegularNilpotent e)
  (isInBorel : 𝔤 → FlagVar → Prop)
  (isInBorel_of_springerMap : ∀ y : CotangentBundle,
    isInBorel (springerMap y) (bundleProjection y))
  (rho_dual : 𝔤)

attribute [instance] SpringerResolutionData.field_k SpringerResolutionData.lieRing
  SpringerResolutionData.lieAlgebra

def SpringerResolutionData.closedEmbedding (D : SpringerResolutionData) :
    D.CotangentBundle → D.FlagVar × D.𝔤 :=
  fun y => (D.bundleProjection y, D.springerMap y)

noncomputable def SpringerResolutionData.mk' (k : Type*) [Field k] (𝔤 : Type*)
    [LieRing 𝔤] [LieAlgebra k 𝔤]
    (FlagVar CotangentBundle : Type*)
    (springerMap : CotangentBundle → 𝔤)
    (bundleProjection : CotangentBundle → FlagVar)
    (IsRegularNilpotent : 𝔤 → Prop)
    (hSpringerMap_mem : ∀ y : CotangentBundle, springerMap y ∈ nilpotentCone k 𝔤)
    (hCotangentBundle_ext : ∀ y₁ y₂ : CotangentBundle,
      bundleProjection y₁ = bundleProjection y₂ →
      springerMap y₁ = springerMap y₂ → y₁ = y₂)
    (hRegNilpMem : ∀ e, IsRegularNilpotent e → e ∈ nilpotentCone k 𝔤)
    (hRegNilpNonempty : ∃ e, IsRegularNilpotent e)
    (isInBorel : 𝔤 → FlagVar → Prop)
    (hIsInBorel_of_springerMap : ∀ y : CotangentBundle,
      isInBorel (springerMap y) (bundleProjection y))
    (rho_dual : 𝔤) :
    SpringerResolutionData where
  k := k
  𝔤 := 𝔤
  FlagVar := FlagVar
  CotangentBundle := CotangentBundle
  springerMap := springerMap
  springerMap_mem_nilpotentCone := hSpringerMap_mem
  bundleProjection := bundleProjection
  cotangentBundle_ext := hCotangentBundle_ext
  IsRegularNilpotent := IsRegularNilpotent
  regularNilpotent_mem := hRegNilpMem
  regularNilpotent_nonempty := hRegNilpNonempty
  isInBorel := isInBorel
  isInBorel_of_springerMap := hIsInBorel_of_springerMap
  rho_dual := rho_dual

structure SkewSymmetricBilinearForm (k : Type*) (M : Type*) [CommRing k]
    [AddCommGroup M] [Module k M] where
  bilin : M →ₗ[k] M →ₗ[k] k
  skew_symm : ∀ x y : M, bilin x y = - bilin y x

def SkewSymmetricBilinearForm.IsNondegenerate {k : Type*} {M : Type*} [CommRing k]
    [AddCommGroup M] [Module k M] (ω : SkewSymmetricBilinearForm k M) : Prop :=
  ∀ x : M, (∀ y : M, ω.bilin x y = 0) → x = 0

def kirillovKostantForm (k : Type*) (𝔤 : Type*) [CommRing k]
    [LieRing 𝔤] [LieAlgebra k 𝔤]
    (f : 𝔤 →ₗ[k] k) : SkewSymmetricBilinearForm k 𝔤 where
  bilin := {
    toFun := fun y => {
      toFun := fun z => f ⁅y, z⁆
      map_add' := by intro z₁ z₂; rw [lie_add, map_add]
      map_smul' := by
        intro r z; rw [lie_smul, map_smul]; simp [RingHom.id_apply, smul_eq_mul]
    }
    map_add' := by
      intro y₁ y₂; ext z
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
      rw [add_lie, map_add]
    map_smul' := by
      intro r y; ext z
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, smul_eq_mul,
        RingHom.id_apply]
      rw [smul_lie, map_smul, smul_eq_mul]
  }
  skew_symm := by
    intro x y
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [← lie_skew, map_neg]

def coadjointStabilizer (k : Type*) (𝔤 : Type*) [CommRing k]
    [LieRing 𝔤] [LieAlgebra k 𝔤]
    (f : 𝔤 →ₗ[k] k) : Submodule k 𝔤 where
  carrier := {x : 𝔤 | ∀ y : 𝔤, f ⁅x, y⁆ = 0}
  add_mem' := by
    intro a b ha hb y
    rw [add_lie, map_add, ha y, hb y, add_zero]
  zero_mem' := by
    intro y; rw [zero_lie, map_zero]
  smul_mem' := by
    intro r a ha y
    rw [smul_lie, map_smul, ha y, smul_zero]

structure CoadjointOrbitData (k : Type*) (𝔤 : Type*) [CommRing k]
    [LieRing 𝔤] [LieAlgebra k 𝔤] where
  G : Type*
  [instGroup : Group G]
  Ad : G →* (𝔤 ≃ₗ[k] 𝔤)
  Ad_preserves_bracket : ∀ (g : G) (x y : 𝔤), Ad g ⁅x, y⁆ = ⁅Ad g x, Ad g y⁆
  coadjointAction : G → (𝔤 →ₗ[k] k) → (𝔤 →ₗ[k] k)
  coadjoint_formula : ∀ (g : G) (f : 𝔤 →ₗ[k] k) (x : 𝔤),
    coadjointAction g f x = f (Ad g⁻¹ x)

attribute [instance] CoadjointOrbitData.instGroup

variable {k' : Type*} {𝔤' : Type*} [CommRing k'] [LieRing 𝔤'] [LieAlgebra k' 𝔤']

def CoadjointOrbitData.orbit (data : CoadjointOrbitData k' 𝔤') (f : 𝔤' →ₗ[k'] k') :
    Set (𝔤' →ₗ[k'] k') :=
  Set.range (fun g => data.coadjointAction g f)

def nilpotentCone_singularLocus (k : Type*) (𝔤 : Type*)
    [CommRing k] [LieRing 𝔤] [LieAlgebra k 𝔤] [Module.Finite k 𝔤] [Module.Free k 𝔤] :
    Set 𝔤 :=
  {x ∈ nilpotentCone k 𝔤 |
    Module.finrank k (LinearMap.ker (LieAlgebra.ad k 𝔤 x : 𝔤 →ₗ[k] 𝔤)) ≠
      LieAlgebra.rank k 𝔤}

structure NilpotentConeOrbitData (k : Type*) (𝔤 : Type*)
    [Field k] [LieRing 𝔤] [LieAlgebra k 𝔤]
    [Module.Finite k 𝔤] [Module.Free k 𝔤] [LieAlgebra.IsSemisimple k 𝔤] where
  dimVariety : Set 𝔤 → ℕ
  dim_nilpCone_eq : dimVariety (nilpotentCone k 𝔤) = Module.finrank k 𝔤 - LieAlgebra.rank k 𝔤
  dim_nilpCone_even : Even (dimVariety (nilpotentCone k 𝔤))
  dim_singLocus_even : Even (dimVariety (nilpotentCone_singularLocus k 𝔤))
  dim_singLocus_lt : dimVariety (nilpotentCone_singularLocus k 𝔤) < dimVariety (nilpotentCone k 𝔤)

structure NilpotentConeCoordRingData (k : Type*) (𝔤 : Type*)
    [Field k] [LieRing 𝔤] [LieAlgebra k 𝔤] where
  SymAlg : Type*
  [symAlgCommRing : CommRing SymAlg]
  [symAlgAlgebra : Algebra k SymAlg]
  eval_𝔤 : SymAlg →ₐ[k] (𝔤 → k)
  vanishingIdeal : Ideal SymAlg
  mem_vanishingIdeal : ∀ f : SymAlg,
    f ∈ vanishingIdeal ↔ ∀ x ∈ nilpotentCone k 𝔤, eval_𝔤 f x = 0
  [symAlg_isNoetherian : IsNoetherianRing SymAlg]
  [vanishingIdeal_isPrime : vanishingIdeal.IsPrime]

attribute [instance] NilpotentConeCoordRingData.symAlgCommRing
  NilpotentConeCoordRingData.symAlgAlgebra
  NilpotentConeCoordRingData.symAlg_isNoetherian
  NilpotentConeCoordRingData.vanishingIdeal_isPrime

abbrev NilpotentConeCoordRingData.coordRing {k : Type*} {𝔤 : Type*}
    [Field k] [LieRing 𝔤] [LieAlgebra k 𝔤]
    (D : NilpotentConeCoordRingData k 𝔤) : Type* :=
  D.SymAlg ⧸ D.vanishingIdeal

theorem nilpotentCone_coordRing_isDomain
    {k : Type*} {𝔤 : Type*} [Field k] [LieRing 𝔤] [LieAlgebra k 𝔤]
    [LieAlgebra.IsSemisimple k 𝔤] [Module.Finite k 𝔤]
    (D : NilpotentConeCoordRingData k 𝔤) : IsDomain D.coordRing :=
  Ideal.Quotient.isDomain D.vanishingIdeal

instance NilpotentConeCoordRingData.instIsDomainCoordRing
    {k : Type*} {𝔤 : Type*} [Field k] [LieRing 𝔤] [LieAlgebra k 𝔤]
    [LieAlgebra.IsSemisimple k 𝔤] [Module.Finite k 𝔤]
    (D : NilpotentConeCoordRingData k 𝔤) : IsDomain D.coordRing :=
  nilpotentCone_coordRing_isDomain D

instance NilpotentConeCoordRingData.instIsNoetherianCoordRing
    {k : Type*} {𝔤 : Type*} [Field k] [LieRing 𝔤] [LieAlgebra k 𝔤]
    (D : NilpotentConeCoordRingData k 𝔤) : IsNoetherianRing D.coordRing :=
  Ideal.Quotient.isNoetherianRing D.vanishingIdeal

def SatisfiesSerreR1 (R : Type*) [CommRing R] : Prop :=
  ∀ (𝔭 : Ideal R) [𝔭.IsPrime], 𝔭.height ≤ 1 →
    IsRegularLocalRing (Localization.AtPrime 𝔭)

def SatisfiesSerreS2 (R : Type*) [CommRing R] : Prop :=
  ∀ (𝔭 : Ideal R) [𝔭.IsPrime], 𝔭.height ≥ 2 →
    ∃ (a b : Localization.AtPrime 𝔭),
      a ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) ∧
      (∀ x : Localization.AtPrime 𝔭, x * a = 0 → x = 0) ∧
      b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) ∧
      (∀ x : Localization.AtPrime 𝔭, x * b ∈ Ideal.span {a} → x ∈ Ideal.span {a})

def IsGradedAlgEquiv {k : Type*} [CommSemiring k]
    {A : Type*} [Semiring A] [Algebra k A]
    {B : Type*} [Semiring B] [Algebra k B]
    (𝒜 : ℕ → Submodule k A) (ℬ : ℕ → Submodule k B)
    (e : A ≃ₐ[k] B) : Prop :=
  ∀ n : ℕ, ∀ a : A, a ∈ 𝒜 n ↔ e a ∈ ℬ n

structure ResolutionData (k : Type*) [Field k] where
  OY : Type*
  [oyCommRing : CommRing OY]
  [oyIsDomain : IsDomain OY]
  [oyAlgebra : Algebra k OY]
  [oyIntegrallyClosed : IsIntegrallyClosed OY]
  [oyNoetherian : IsNoetherianRing OY]
  OX : Type*
  [oxCommRing : CommRing OX]
  [oxIsDomain : IsDomain OX]
  [oxAlgebra : Algebra k OX]
  pStar : OY →+* OX
  hProper : letI : Algebra OY OX := pStar.toAlgebra; Algebra.IsIntegral OY OX
  hFracIso : ∃ (φ : FractionRing OY ≃+* FractionRing OX),
    ∀ r : OY, φ (algebraMap OY (FractionRing OY) r) =
      algebraMap OX (FractionRing OX) (pStar r)

attribute [instance] ResolutionData.oyCommRing ResolutionData.oyIsDomain
  ResolutionData.oyAlgebra ResolutionData.oyIntegrallyClosed
  ResolutionData.oyNoetherian ResolutionData.oxCommRing
  ResolutionData.oxIsDomain ResolutionData.oxAlgebra

noncomputable def ResolutionData.mk' (k : Type*) [Field k]
    (OY : Type*) [CommRing OY] [IsDomain OY] [Algebra k OY]
    [IsIntegrallyClosed OY] [IsNoetherianRing OY]
    (OX : Type*) [CommRing OX] [IsDomain OX] [Algebra k OX]
    (pStar : OY →+* OX)
    (hProper : letI : Algebra OY OX := pStar.toAlgebra; Algebra.IsIntegral OY OX)
    (hFracIso : ∃ (φ : FractionRing OY ≃+* FractionRing OX),
      ∀ r : OY, φ (algebraMap OY (FractionRing OY) r) =
        algebraMap OX (FractionRing OX) (pStar r)) : ResolutionData k where
  OY := OY
  OX := OX
  pStar := pStar
  hProper := hProper
  hFracIso := hFracIso
