/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BernsteinGelfandEquivalence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.HCBimoduleProjectives.Part2
import Lemma.Fin.All_Eq.of.All_Eq.All_Eq_RightAction.All_Eq_RightAction.All_Any_Eq_Sum_RightAction
import Lemma.Int.IsInQPlus0
import Lemma.Int.WeightLE.of.BruhatLE
import Lemma.Int.Level1.ne.Top
import Lemma.Int.FGUeaIotaRange
import Def.v1.Atlas.LieGroups.code.CategoryO.Part3
import Def.v1.Atlas.LieGroups.code.CategoryOII.Part3
import Def.v1.Atlas.LieGroups.code.JantzenFiltration.Part2
import Def.v1.Atlas.LieGroups.code.DufloJoseph.Part8
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Analysis.Complex.Basic
import Def.v1.Atlas.LieGroups.code.BernsteinGelfandEquivalence.Part3


noncomputable section

open TensorProduct

universe u_R u_g u_mod

attribute [instance] LieModuleObj.instAddCommGroup LieModuleObj.instModule
  LieModuleObj.instLieRingModule LieModuleObj.instLieModule

variable {R : Type u_R} [CommRing R]

variable {g : Type u_g} [LieRing g] [LieAlgebra R g]

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

end
