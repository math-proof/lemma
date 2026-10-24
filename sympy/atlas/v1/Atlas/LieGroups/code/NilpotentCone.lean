/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/NilpotentCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.Rank
import Mathlib.Algebra.Lie.CartanExists
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Basic
import Mathlib.Topology.Irreducible
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.Spectrum.Prime.Topology

noncomputable section

open scoped LieAlgebra
open Set

namespace LieAlgebra

variable (R : Type*) [CommRing R]
variable (L : Type*) [LieRing L] [LieAlgebra R L]

def IsNilpotentElement (x : L) : Prop :=
  IsNilpotent (LieAlgebra.ad R L x)

def NilpotentCone : Set L :=
  {x : L | IsNilpotentElement R L x}

structure AdjointGroupAction where
  G : Type*
  instGroup : Group G
  Ad : G → L ≃ₗ⁅R⁆ L
  Ad_mul : ∀ g₁ g₂ : G,
    (Ad (@HMul.hMul G G G (@instHMul G instGroup.toMul) g₁ g₂) : L → L) =
    (Ad g₁ : L → L) ∘ (Ad g₂ : L → L)
  Ad_one : Ad (@One.one G instGroup.toOne) = LieEquiv.refl
  instTopologicalSpaceG : TopologicalSpace G
  instIrreducibleSpaceG : @IrreducibleSpace G instTopologicalSpaceG
  orbit_map_continuous : ∀ (ts : TopologicalSpace L) (x : L),
    @Continuous G L instTopologicalSpaceG ts (fun g => Ad g x)

variable {R L}

def AdjointOrbit (Gact : AdjointGroupAction R L) (x : L) : Set L :=
  { y : L | ∃ g : Gact.G, Gact.Ad g x = y }

def IsAdjointConjugate (Gact : AdjointGroupAction R L) (x y : L) : Prop :=
  ∃ g : Gact.G, Gact.Ad g x = y

def lieCentralizer (x : L) : Submodule R L :=
  LinearMap.ker (LieAlgebra.ad R L x : L →ₗ[R] L)

variable [Module.Finite R L] [Module.Free R L]

def IsRegularElement (x : L) : Prop :=
  Module.finrank R (lieCentralizer R L x) = LieAlgebra.rank R L

def IsRegularNilpotent (x : L) : Prop :=
  IsNilpotentElement R L x ∧ IsRegularElement R L x

section PrincipalSl2

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
  [LieAlgebra.IsSemisimple ℂ 𝔤]
  [Module.Finite ℂ 𝔤] [Module.Free ℂ 𝔤]

def IsAdInvariant (x : 𝔤) (V : Submodule ℂ 𝔤) : Prop :=
  ∀ v ∈ V, (LieAlgebra.ad ℂ 𝔤 x) v ∈ V

def IsSl2SubmoduleOf (h e f : 𝔤) (V : Submodule ℂ 𝔤) : Prop :=
  IsAdInvariant h V ∧ IsAdInvariant e V ∧ IsAdInvariant f V

def IsSl2IrreducibleSubmoduleOf (h e f : 𝔤) (V : Submodule ℂ 𝔤) : Prop :=
  V ≠ ⊥ ∧ IsSl2SubmoduleOf h e f V ∧
  ∀ W : Submodule ℂ 𝔤, W ≤ V → IsSl2SubmoduleOf h e f W → W = ⊥ ∨ W = V

def IsSl2SubmoduleOf.toLieSubmodule {h e f : 𝔤} (t : IsSl2Triple h e f)
    {V : Submodule ℂ 𝔤} (hV : IsSl2SubmoduleOf h e f V) :
    LieSubmodule ℂ (↥(t.toLieSubalgebra ℂ)) 𝔤 where
  __ := V
  lie_mem {x v} hv := by
    obtain ⟨c₁, c₂, c₃, hx⟩ := IsSl2Triple.mem_toLieSubalgebra_iff.mp x.2
    have hv_h := hV.1 v hv
    have hv_e := hV.2.1 v hv
    have hv_f := hV.2.2 v hv

    have heq : ⁅(x : 𝔤), v⁆ = c₁ • ⁅e, v⁆ + c₂ • ⁅f, v⁆ + c₃ • ⁅h, v⁆ := by
      rw [hx, add_lie, add_lie, smul_lie, smul_lie, smul_lie, t.lie_e_f]
    show ⁅(x : 𝔤), v⁆ ∈ V
    rw [heq]
    exact V.add_mem (V.add_mem (V.smul_mem _ hv_e) (V.smul_mem _ hv_f)) (V.smul_mem _ hv_h)

def IsSl2IrreducibleLieSubmodule {h e f : 𝔤} (t : IsSl2Triple h e f)
    (V : LieSubmodule ℂ (↥(t.toLieSubalgebra ℂ)) 𝔤) : Prop :=
  V ≠ ⊥ ∧
  ∀ W : LieSubmodule ℂ (↥(t.toLieSubalgebra ℂ)) 𝔤,
    W.toSubmodule ≤ V.toSubmodule → W = ⊥ ∨ W = V

structure RootSystemData (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    [Module.Finite ℂ 𝔤] [Module.Free ℂ 𝔤] where
  rankVal : ℕ
  rank_pos : 0 < rankVal
  rank_eq : rankVal = LieAlgebra.rank ℂ 𝔤
  simpleRootVector : Fin rankVal → 𝔤
  simpleCorootVector : Fin rankVal → 𝔤
  simpleCoroot : Fin rankVal → 𝔤
  halfSumPosCoroots : 𝔤
  lie_simpleRootVector_simpleCorootVector :
    ∀ i j : Fin rankVal,
      ⁅simpleRootVector i, simpleCorootVector j⁆ =
        if i = j then simpleCoroot i else 0
  simpleRootVector_ne_zero : ∀ i : Fin rankVal, simpleRootVector i ≠ 0
  simpleCorootVector_ne_zero : ∀ i : Fin rankVal, simpleCorootVector i ≠ 0
  halfSumPosCoroots_regular :
    Module.finrank ℂ (lieCentralizer ℂ 𝔤 halfSumPosCoroots) = LieAlgebra.rank ℂ 𝔤
  no_joint_centralizer :
    ∀ v : 𝔤, ⁅halfSumPosCoroots, v⁆ = 0 →
      ⁅∑ i, simpleRootVector i, v⁆ = 0 → v = 0
  halfSumPosCoroots_odd_dim_irreducibles :
    ∀ {h e f : 𝔤} (_hprinc_h : h = (2 : ℂ) • halfSumPosCoroots)
      (_hprinc_e : e = ∑ i, simpleRootVector i)
      {V : Submodule ℂ 𝔤} (_hirr : IsSl2IrreducibleSubmoduleOf h e f V),
      ¬ Even (Module.finrank ℂ V)

structure IsPrincipalSl2Triple (h e f : 𝔤) extends IsSl2Triple h e f where
  rootData : RootSystemData 𝔤
  e_eq_sum : e = ∑ i, rootData.simpleRootVector i
  h_eq_two_rho : h = (2 : ℂ) • rootData.halfSumPosCoroots
  e_nilpotent : IsNilpotentElement ℂ 𝔤 e

omit [IsSemisimple ℂ 𝔤] [Module.Free ℂ 𝔤] in
structure BorelSubgroupData (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    [Module.Finite ℂ 𝔤] [Module.Free ℂ 𝔤]
    (rsd : RootSystemData 𝔤) where
  B : Type*
  instGroupB : Group B
  AdB : B → 𝔤 ≃ₗ⁅ℂ⁆ 𝔤
  AdB_mul : ∀ b₁ b₂ : B,
    (@AdB (@HMul.hMul B B B (@instHMul B instGroupB.toMul) b₁ b₂) : 𝔤 → 𝔤) =
    (AdB b₁ : 𝔤 → 𝔤) ∘ (AdB b₂ : 𝔤 → 𝔤)
  numPosRoots : ℕ
  rootVector : Fin numPosRoots → 𝔤
  isSimple : Fin numPosRoots → Prop
  instDecSimple : DecidablePred isSimple
  numSimple_eq_rank : (Finset.univ.filter (fun i => @decide (isSimple i) (instDecSimple i))).card
    = rsd.rankVal
  simpleRootVectorBij : Fin rsd.rankVal → Fin numPosRoots
  simpleRootVectorBij_isSimple : ∀ j, isSimple (simpleRootVectorBij j)
  simpleRootVectorBij_surj : ∀ i, isSimple i → ∃ j, simpleRootVectorBij j = i
  simpleRootVector_eq : ∀ j, rootVector (simpleRootVectorBij j) = rsd.simpleRootVector j
  H_torus : Type*
  instGroupH : Group H_torus
  embedH : @H_torus → B
  N_unip : Type*
  instGroupN : Group N_unip
  embedN : @N_unip → B
  torus_scaling : @H_torus → Fin numPosRoots → ℂˣ
  levi_decomp : ∀ (b : B),
    ∃ (t : @H_torus) (n : @N_unip),
      ∀ (x : 𝔤), (AdB b : 𝔤 → 𝔤) x =
        (AdB (@embedH t) : 𝔤 → 𝔤) ((AdB (@embedN n) : 𝔤 → 𝔤) x)
  unip_orbit_fwd : ∀ (n : @N_unip),
    ∃ (c : Fin numPosRoots → ℂ),
      (∀ i, isSimple i → c i = 1) ∧
      (@AdB (@embedN n) : 𝔤 → 𝔤)
          (∑ j : Fin rsd.rankVal, rootVector (simpleRootVectorBij j))
        = ∑ i, c i • rootVector i
  unip_orbit_bwd : ∀ (c : Fin numPosRoots → ℂ),
    (∀ i, isSimple i → c i = 1) →
    ∃ (n : @N_unip),
      (@AdB (@embedN n) : 𝔤 → 𝔤)
          (∑ j : Fin rsd.rankVal, rootVector (simpleRootVectorBij j))
        = ∑ i, c i • rootVector i
  torus_action_eq : ∀ (t : @H_torus) (i : Fin numPosRoots),
    (@AdB (@embedH t) : 𝔤 → 𝔤) (rootVector i) =
      (torus_scaling t i : ℂ) • rootVector i
  torus_simple_surj : ∀ (s : Fin rsd.rankVal → ℂˣ),
    ∃ (t : @H_torus), ∀ j, torus_scaling t (simpleRootVectorBij j) = s j

def BorelSubgroupData.regularNilpotentSet {rsd : RootSystemData 𝔤}
    (BD : BorelSubgroupData 𝔤 rsd) : Set 𝔤 :=
  { x : 𝔤 | ∃ (c : Fin BD.numPosRoots → ℂ),
      (∀ i, BD.isSimple i → c i ≠ 0) ∧
      x = ∑ i, c i • BD.rootVector i }

def BorelSubgroupData.borelOrbit {rsd : RootSystemData 𝔤}
    (BD : BorelSubgroupData 𝔤 rsd) (e : 𝔤) : Set 𝔤 :=
  { y : 𝔤 | ∃ b : BD.B, @BD.AdB b e = y }

structure NilpotentConeCoordinateRing [LieAlgebra.IsSemisimple ℂ 𝔤] where
  carrier : Type*
  instCommRing : CommRing carrier
  instAlgebra : Algebra ℂ carrier
  instNontrivial : Nontrivial carrier
  genericFiber : Type*
  instGenericFiberCommRing : CommRing genericFiber
  toGenericFiber : @RingHom carrier genericFiber
    instCommRing.toNonAssocRing.toNonAssocSemiring
    instGenericFiberCommRing.toNonAssocRing.toNonAssocSemiring
  instCarrierGenericFiberAlg : @Algebra carrier genericFiber
    instCommRing.toCommSemiring instGenericFiberCommRing.toSemiring
  locSubmonoid : @Submonoid carrier instCommRing.toMulOneClass
  locSubmonoid_le_nonZeroDivisors :
    ∀ s ∈ locSubmonoid, s ∈ @nonZeroDivisors carrier instCommRing.toMonoidWithZero
  instIsLocalization : @IsLocalization carrier instCommRing.toCommSemiring
    locSubmonoid genericFiber instGenericFiberCommRing.toCommSemiring
    instCarrierGenericFiberAlg
  toGenericFiber_eq : toGenericFiber = @algebraMap carrier genericFiber
    instCommRing.toCommSemiring instGenericFiberCommRing.toSemiring
    instCarrierGenericFiberAlg
  instGenericFiberSemisimple : @IsSemisimpleRing genericFiber
    instGenericFiberCommRing.toRing

def maximalQuotientIdeal_17
    (χ : ↥(Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤)) →ₐ[ℂ] ℂ) :
    TwoSidedIdeal (UniversalEnvelopingAlgebra ℂ 𝔤) :=
  TwoSidedIdeal.span
    { x | ∃ (z : ↥(Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤))),
      x = (z : UniversalEnvelopingAlgebra ℂ 𝔤) - algebraMap ℂ _ (χ z) }

abbrev MaximalQuotient_17
    (χ : ↥(Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤)) →ₐ[ℂ] ℂ) :=
  (maximalQuotientIdeal_17 𝔤 χ).ringCon.Quotient

def HasDomainAssociatedGraded (R : Type*) [Ring R] : Prop :=
  ∃ (v : R → WithBot ℤ),
    v 0 = ⊥ ∧
    v 1 ≠ ⊥ ∧
    (∀ a : R, a ≠ 0 → v a ≠ ⊥) ∧
    (∀ a b : R, a ≠ 0 → b ≠ 0 → v (a * b) = v a + v b)

structure SubMulFiltrationDomain (R : Type*) [Ring R] where
  v : R → WithBot ℤ
  v_zero : v 0 = ⊥
  v_one : v 1 ≠ ⊥
  v_nonzero : ∀ a : R, a ≠ 0 → v a ≠ ⊥
  v_submul : ∀ a b : R, a ≠ 0 → b ≠ 0 → v a + v b ≤ v (a * b)
  gr_domain : ∀ a b : R, a ≠ 0 → b ≠ 0 → ¬(v a + v b < v (a * b))

structure SubMulFiltration (R : Type*) [Ring R] where
  v : R → WithBot ℤ
  v_zero : v 0 = ⊥
  v_one : v 1 ≠ ⊥
  v_nonzero : ∀ a : R, a ≠ 0 → v a ≠ ⊥
  v_submul : ∀ a b : R, a ≠ 0 → b ≠ 0 → v a + v b ≤ v (a * b)

def SubMulFiltration.toSubMulFiltrationDomain {R : Type*} [Ring R]
    (F : SubMulFiltration R)
    (hgr : ∀ a b : R, a ≠ 0 → b ≠ 0 → ¬(F.v a + F.v b < F.v (a * b))) :
    SubMulFiltrationDomain R :=
  { v := F.v
    v_zero := F.v_zero
    v_one := F.v_one
    v_nonzero := F.v_nonzero
    v_submul := F.v_submul
    gr_domain := hgr }

structure PBWSymbolData {R : Type*} [Ring R] (v : R → WithBot ℤ) where
  D : Type
  instRing : Ring D
  instDomain : @IsDomain D instRing.toSemiring
  σ : R → D
  σ_nonzero : ∀ a : R, a ≠ 0 → σ a ≠ 0
  σ_cancel : ∀ a b : R, a ≠ 0 → b ≠ 0 → v a + v b < v (a * b) → σ a * σ b = 0
