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
import Def.v1.Atlas.LieGroups.code.NilpotentCone.Part2


noncomputable section

open scoped LieAlgebra

open Set

namespace LieAlgebra

variable (R : Type*) [CommRing R]

variable (L : Type*) [LieRing L] [LieAlgebra R L]

variable {R L}

variable [Module.Finite R L] [Module.Free R L]

section PrincipalSl2

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
  [LieAlgebra.IsSemisimple ℂ 𝔤]
  [Module.Finite ℂ 𝔤] [Module.Free ℂ 𝔤]

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

end PrincipalSl2
end LieAlgebra
end
