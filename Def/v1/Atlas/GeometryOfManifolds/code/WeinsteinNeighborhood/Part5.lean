/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticLinearAlgebra
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.MoserDarboux
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Structure.v1.Atlas.GeometryOfManifolds.code.MoserDarboux.Part2
import Def.v1.Atlas.GeometryOfManifolds.code.BlockMatrixLp
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.ODE.PicardLindelof
import Structure.v1.Atlas.GeometryOfManifolds.code.WeinsteinNeighborhood.Part4
set_option autoImplicit false

open Module FiniteDimensional
open SymplecticLinearAlgebra
open DifferentialFormSpace


/-- **Tubular neighborhood theorem (assembly).** Given an exponential map data and the
output of the inverse function theorem, this assembles the full tubular neighborhood
data: $X \subseteq M$ admits a tubular neighborhood $U_1 \cong U_0 \subseteq NX$. -/
def tubular_neighborhood_theorem
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_NX : ℕ → Type*} {VF_NX : Type*}
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_NX : DifferentialFormSpace Ω_NX VF_NX]
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    (nb : NormalBundleDFS Ω_X VF_X Ω_NX VF_NX)
    (i : DFSMorphism Ω_X VF_X Ω_M VF_M)
    (dimM dimX : ℕ)
    (hSubmfd : IsSubmanifoldInclusion i dimM dimX)

    [expData : HasTubularExpMapData nb i dimM dimX hSubmfd]

    [iftData : @HasIFTData Ω_X VF_X Ω_NX VF_NX Ω_M VF_M
      expData.Ω_U₀ expData.VF_U₀
      inst_X inst_NX inst_M expData.inst_U₀
      nb i expData.exp_map expData.j₀ expData.s₀
      expData.hU₀_nbhd expData.hd_exp_id] :
    @TubularNeighborhoodData Ω_X VF_X Ω_NX VF_NX Ω_M VF_M
      inst_X inst_NX inst_M nb i :=


  letI : DifferentialFormSpace expData.Ω_U₀ expData.VF_U₀ := expData.inst_U₀
  letI : DifferentialFormSpace iftData.Ω_U₁ iftData.VF_U₁ := iftData.inst_U₁
  { Ω_U₀ := expData.Ω_U₀
    VF_U₀ := expData.VF_U₀
    inst_U₀ := expData.inst_U₀
    Ω_U₁ := iftData.Ω_U₁
    VF_U₁ := iftData.VF_U₁
    inst_U₁ := iftData.inst_U₁
    φ := iftData.φ
    φ_inv := iftData.φ_inv
    j₀ := expData.j₀
    s₀ := expData.s₀

    j₁ :=
      { pullback := fun α => expData.s₀.pullback (iftData.φ.pullback α)
        pullback_add := fun α β => by simp [iftData.φ.pullback_add, expData.s₀.pullback_add]
        pullback_smul := fun r α => by simp [iftData.φ.pullback_smul, expData.s₀.pullback_smul]
        pullback_comm_d := fun α => by simp [iftData.φ.pullback_comm_d, expData.s₀.pullback_comm_d] }
    incl_U₁_M := iftData.incl_U₁_M
    hDiffeo := iftData.hDiffeo
    hU₀_nbhd := expData.hU₀_nbhd

    hU₁_nbhd := ⟨fun α => by


      show expData.s₀.pullback (iftData.φ.pullback (iftData.incl_U₁_M.pullback α)) = i.pullback α

      rw [iftData.exp_factors α]

      exact expData.hd_exp_id α⟩

    hφ_X := fun _ => rfl }


/-- The 2-form $\omega$ has the property that contraction $v \mapsto \iota_v \omega$
hits every 1-form — equivalently, $\omega^\flat : TM \to T^*M$ is surjective. -/
def ContractionSurjective
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (ω : Ω 2) : Prop :=
  ∀ (α : Ω 1), ∃ (v : VF), inst.ι v ω = α

/-- The DFS morphism $i : U \hookrightarrow M$ comes from a *proper* open inclusion
$U \subsetneq M$: pullback on smooth functions is not surjective. -/
def IsProperSubDFS {Ω₁ : ℕ → Type*} {VF₁ : Type*} [DifferentialFormSpace Ω₁ VF₁]
    {Ω₂ : ℕ → Type*} {VF₂ : Type*} [DifferentialFormSpace Ω₂ VF₂]
    (i : DFSMorphism Ω₁ VF₁ Ω₂ VF₂) : Prop :=
  ¬ Function.Surjective (fun (α : Ω₂ 0) => i.pullback α)

