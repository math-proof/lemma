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


noncomputable section

universe uCatO

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

def HasStandardFiltration
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (V : Type uCatO) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (_hV : IsCategoryO Δ rd V) : Prop :=
  ∃ (n : ℕ) (F : Fin (n + 1) → LieSubmodule R 𝔤 V),
    F ⟨0, Nat.zero_lt_succ n⟩ = ⊥ ∧
    F ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ = ⊤ ∧
    (∀ i : Fin n, F i.castSucc < F i.succ) ∧


    (∀ i : Fin n, ∃ (lam_i : Δ.𝔥 →ₗ[R] R)
      (Q : Type uCatO) (_ : AddCommGroup Q) (_ : Module R Q)
      (_ : LieRingModule 𝔤 Q) (_ : LieModule R 𝔤 Q)
      (_ : IsVermaModule Δ Q lam_i)
      (π : ↥(F i.succ) →ₗ⁅R, 𝔤⁆ Q),
      Function.Surjective π ∧
      (∀ x : ↥(F i.succ), π x = 0 ↔ (x : V) ∈ F i.castSucc))

def Ext1VanishingForContragredientVerma
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (X : Type uCatO) [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (_hXO : IsCategoryO Δ rd X) : Prop :=
  ∀ (lam : Δ.𝔥 →ₗ[R] R)
    (MlamDual : Type uCatO) [AddCommGroup MlamDual] [Module R MlamDual]
    [LieRingModule 𝔤 MlamDual] [LieModule R 𝔤 MlamDual]
    (hMlamDualO : IsCategoryO Δ rd MlamDual)
    (_hContra : IsContragredientVerma rd MlamDual lam hMlamDualO)
    (E : Type uCatO) [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    (_hEO : IsCategoryO Δ rd E)
    (i : MlamDual →ₗ⁅R, 𝔤⁆ E) (_hi : Function.Injective i)
    (p : E →ₗ⁅R, 𝔤⁆ X) (_hp : Function.Surjective p)

    (_hexact : ∀ e : E, p e = 0 ↔ ∃ m : MlamDual, i m = e),
    ∃ (s : X →ₗ⁅R, 𝔤⁆ E), ∀ x, p (s x) = x

noncomputable def CategoryO.compositionLengthO
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (X : Type uCatO) [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X) : ℕ :=
  (Classical.choice (categoryO_has_composition_series hXO)).length

end
