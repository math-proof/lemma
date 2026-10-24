/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import sympy.atlas.v1.Atlas.LieGroups.code.ContinuousRep
import Lemma.Complex.IsStronglyContinuousToMonoidHom
import Lemma.Complex.IsKFinite0
import Lemma.Real.GetToMonoidHom.in.SmoothSubspace.of.In_SmoothSubspace
import Lemma.Complex.inner.of.IsUnitary
import Lemma.Real.IsSmoothVector0
import Lemma.Complex.Eq_Sum_Mul
import sympy.atlas.v1.Atlas.LieGroups.code.KFinite
import sympy.atlas.v1.Atlas.LieGroups.code.SmoothVectors
import sympy.atlas.v1.Atlas.LieGroups.code.KFiniteProps
import sympy.atlas.v1.Atlas.LieGroups.code.IsotypicPeterWeyl
import sympy.atlas.v1.Atlas.LieGroups.code.SmoothVectorsProps
import sympy.atlas.v1.Atlas.LieGroups.code.CompactMeasures

set_option autoImplicit false

open scoped Topology Manifold
open MeasureTheory

noncomputable section

namespace PlancherelCompact

structure IrrFinDimRep (K : Type*) [Group K] [TopologicalSpace K]
    [CompactSpace K] where
  carrier : Type
  [instNormedAddCommGroup : NormedAddCommGroup carrier]
  [instInnerProductSpace : InnerProductSpace ℂ carrier]
  [instFiniteDimensional : FiniteDimensional ℂ carrier]
  [instCompleteSpace : CompleteSpace carrier]
  rep : ContinuousRep K carrier
  irred : rep.IsIrreducible
  unitary : rep.IsUnitary
  [nontrivial : Nontrivial carrier]

attribute [instance] IrrFinDimRep.instNormedAddCommGroup
  IrrFinDimRep.instInnerProductSpace IrrFinDimRep.instFiniteDimensional
  IrrFinDimRep.instCompleteSpace IrrFinDimRep.nontrivial

def IrrFinDimRep.dim {K : Type*} [Group K] [TopologicalSpace K]
    [CompactSpace K] (ρ : IrrFinDimRep K) : ℕ :=
  Module.finrank ℂ ρ.carrier

def IrrFinDimRep.repFourierCoeff {K : Type*} [Group K] [TopologicalSpace K]
    [CompactSpace K] [MeasureSpace K]
    (ρ : IrrFinDimRep K) (f : K → ℂ) : ρ.carrier →L[ℂ] ρ.carrier :=
  ∫ k, f k • ρ.rep.toMonoidHom k

def IrrFinDimRep.plancherelTerm {K : Type*} [Group K] [TopologicalSpace K]
    [CompactSpace K] [MeasureSpace K]
    (ρ : IrrFinDimRep K) (f₁ f₂ : K → ℂ) : ℂ :=
  (Module.finrank ℂ ρ.carrier : ℂ) *
    LinearMap.trace ℂ ρ.carrier
      (((ρ.repFourierCoeff f₁).comp
        (ContinuousLinearMap.adjoint (ρ.repFourierCoeff f₂)) : ρ.carrier →L[ℂ] ρ.carrier) :
          ρ.carrier →ₗ[ℂ] ρ.carrier)

def IrrFinDimRep.plancherelSingleTerm {K : Type*} [Group K] [TopologicalSpace K]
    [CompactSpace K] [MeasureSpace K]
    (ρ : IrrFinDimRep K) (f : K → ℂ) : ℂ :=
  (Module.finrank ℂ ρ.carrier : ℂ) *
    LinearMap.trace ℂ ρ.carrier
      ((ρ.repFourierCoeff f : ρ.carrier →L[ℂ] ρ.carrier) : ρ.carrier →ₗ[ℂ] ρ.carrier)

abbrev PeterWeylIndex
    {K : Type*} [Group K] [TopologicalSpace K] [CompactSpace K]
    (ι : Type*) (ρ : ι → IrrFinDimRep K) :=
  (i : ι) × (Fin (ρ i).dim × Fin (ρ i).dim)

section proposition_4_1

end proposition_4_1

def convolutionOp
    {K : Type*} [Group K] [TopologicalSpace K]
    [CompactSpace K] [MeasureSpace K]
    (f : K → ℂ) (ψ : K → ℂ) : K → ℂ :=
  fun x => ∫ y, f (x * y⁻¹) * ψ y

def convolutionKernel
    {K : Type*} [Group K]
    (f : K → ℂ) : K → K → ℂ :=
  fun x y => f (x * y⁻¹)

def convolutionKernelDiagIntegral
    {K : Type*} [Group K] [TopologicalSpace K]
    [CompactSpace K] [MeasureSpace K]
    (f : K → ℂ) : ℂ :=
  ∫ x : K, convolutionKernel f x x

def IsKFiniteFunction
    (K : Type*) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] (f : K → ℂ) : Prop :=
  ∃ (n : ℕ)
    (mc : Fin n → (K → ℂ))
    (c : Fin n → ℂ),

    (∀ i, ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W)
          (_ : TopologicalSpace W) (_ : FiniteDimensional ℂ W)
          (ρ : ContinuousRep K W) (φ : W →L[ℂ] ℂ) (v : W),
          mc i = ContinuousRep.matrixCoefficient K ρ φ v) ∧
    (∀ g, f g = ∑ i, c i * mc i g)

noncomputable def leftRegularRep_CK
    (K : Type*) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] :
    ContinuousRep K C(K, ℂ) where
  toMonoidHom :=
    { toFun := fun g =>
        { toFun := fun f => f.comp ⟨fun x => g⁻¹ * x, continuous_const.mul continuous_id⟩
          map_add' := fun f₁ f₂ => by ext x; simp [ContinuousMap.comp]
          map_smul' := fun c f => by ext x; simp [ContinuousMap.comp]
          cont := (⟨fun x => g⁻¹ * x, continuous_const.mul continuous_id⟩ : C(K, K)).continuous_precomp }
      map_one' := by
        ext f x
        simp [ContinuousMap.comp]
      map_mul' := fun g h => by
        ext f x
        simp [ContinuousMap.comp, mul_inv_rev, mul_assoc] }
  continuous_action := by

    show Continuous (fun p : K × C(K, ℂ) =>
      p.2.comp ⟨fun x => p.1⁻¹ * x, continuous_const.mul continuous_id⟩)

    have h_left : Continuous (fun g : K => (⟨fun x => g⁻¹ * x, continuous_const.mul continuous_id⟩ : C(K, K))) :=
      ContinuousMap.continuous_of_continuous_uncurry _ (continuous_fst.inv.mul continuous_snd)

    have h_comp : Continuous (fun q : C(K, K) × C(K, ℂ) => q.2.comp q.1) :=
      ContinuousMap.continuous_comp'

    exact h_comp.comp (Continuous.prodMk (h_left.comp continuous_fst) continuous_snd)

noncomputable def contragredientFinRep
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (K : Type*) [Group K] [TopologicalSpace K] [CompactSpace K]
    (ρ : Representation ℂ K V) [FiniteDimensional ℂ V] :
    Representation ℂ K (V →ₗ[ℂ] ℂ) where
  toFun k :=
    { toFun := fun φ => φ.comp (ρ k⁻¹)
      map_add' := fun φ₁ φ₂ => by simp only [LinearMap.add_comp]
      map_smul' := fun c φ => by simp only [LinearMap.smul_comp, RingHom.id_apply] }
  map_one' := by
    ext φ v
    simp
  map_mul' := fun g h => by
    ext φ v
    simp [mul_inv_rev]

abbrev IsSmoothVector
    {G : Type*} [Group G] [TopologicalSpace G]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
    {HG : Type*} [TopologicalSpace HG]
    (IG : ModelWithCorners ℝ EG HG) [ChartedSpace HG G] [LieGroup IG ⊤ G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (v : F) : Prop :=
  π.IsSmoothVector IG v

abbrev smoothVectors
    {G : Type*} [Group G] [TopologicalSpace G]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
    {HG : Type*} [TopologicalSpace HG]
    (IG : ModelWithCorners ℝ EG HG) [ChartedSpace HG G] [LieGroup IG ⊤ G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) : Submodule ℂ F :=
  π.smoothSubspace IG
