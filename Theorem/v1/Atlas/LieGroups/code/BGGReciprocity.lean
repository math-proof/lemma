/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.CompositionSeries
import Lemma.Int.StandardFiltrationMultiplicity.eq.DimHomProjectiveContragredientVerma
import Def.v1.Atlas.LieGroups.code.DualityFunctorDefs
import Def.v1.Atlas.LieGroups.code.BGGReciprocity


noncomputable section

universe uCatO

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

theorem UEA_induction_on_gen
    {R : Type*} [CommRing R]
    {L : Type*} [LieRing L] [LieAlgebra R L]
    {C : UniversalEnvelopingAlgebra R L → Prop}
    (u : UniversalEnvelopingAlgebra R L)
    (h_alg : ∀ r : R, C (algebraMap R _ r))
    (h_ι : ∀ x : L, C (UniversalEnvelopingAlgebra.ι R x))
    (h_mul : ∀ a b, C a → C b → C (a * b))
    (h_add : ∀ a b, C a → C b → C (a + b)) :
    C u := by
  obtain ⟨t, rfl⟩ := RingQuot.mkAlgHom_surjective R
    (UniversalEnvelopingAlgebra.Rel R L) u
  change C ((UniversalEnvelopingAlgebra.mkAlgHom R L) t)
  induction t using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact h_alg r
  | ι x => exact h_ι x
  | mul a b ha hb => rw [map_mul]; exact h_mul _ _ ha hb
  | add a b ha hb => rw [map_add]; exact h_add _ _ ha hb


theorem lieModuleHom_ueaSubalg_compat_gen
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M N : Type*} [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (f : M →ₗ⁅R, 𝔤⁆ N)
    (u : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg) (m : M) :
    f ((ueaSubalgAction Δ.𝔫_neg M u) m) = (ueaSubalgAction Δ.𝔫_neg N u) (f m) := by
  suffices h : ∀ m, f ((ueaSubalgAction Δ.𝔫_neg M u) m) =
      (ueaSubalgAction Δ.𝔫_neg N u) (f m) from h m
  induction u using UEA_induction_on_gen with
  | h_alg r =>
    intro m
    simp only [ueaSubalgAction, Algebra.algebraMap_eq_smul_one]
    simp [LinearMap.smul_apply, map_smul]
  | h_ι x =>
    intro m
    simp only [ueaSubalgAction, UniversalEnvelopingAlgebra.lift_ι_apply,
      LieModule.toEnd_apply_apply]
    exact f.map_lie x m
  | h_mul a b ha hb =>
    intro m
    simp only [map_mul]
    change f ((ueaSubalgAction Δ.𝔫_neg M a).comp (ueaSubalgAction Δ.𝔫_neg M b) m) =
           (ueaSubalgAction Δ.𝔫_neg N a).comp (ueaSubalgAction Δ.𝔫_neg N b) (f m)
    simp only [LinearMap.comp_apply]
    rw [ha ((ueaSubalgAction Δ.𝔫_neg M b) m)]
    congr 1
    exact hb m
  | h_add a b ha hb =>
    intro m
    simp only [map_add, LinearMap.add_apply, map_add]
    rw [ha m, hb m]


end
