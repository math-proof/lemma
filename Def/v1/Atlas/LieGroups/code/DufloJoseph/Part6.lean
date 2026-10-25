/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.LieGroups.code.MaximalQuotients
import Lemma.Int.Any_EqUeaAction
import Lemma.Fin.Any_Eq.of.Ne_0
import Lemma.Complex.Any_Any_And_All_Eq_AdjointAction.All_Finite.of.IsHarishChandraBimodule.IsIrreducible
import Def.v1.Atlas.LieGroups.code.HighestWeightModules.Part2
import Theorem.v1.Atlas.LieGroups.code.HarishChandraCorollaries
import Theorem.v1.Atlas.LieGroups.code.DufloJoseph.Part5


noncomputable section

variable {R : Type*} [CommRing R]

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

def tensorHomMap
    (V : Type*) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V] [Module.Finite R V]
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M] :
    TensorProduct R V (HomFin (R := R) (𝔤 := 𝔤) M M) →ₗ[R]
      HomFin (R := R) (𝔤 := 𝔤) M (TensorProduct R V M) :=
  TensorProduct.lift
    { toFun := fun v =>
        { toFun := fun f =>
            ⟨(TensorProduct.mk R V M v).comp (f : M →ₗ[R] M),
             isFiniteTypeMap_comp_mk_tensor V v (f : M →ₗ[R] M) f.property⟩
          map_add' := fun f₁ f₂ => by
            apply Subtype.ext; ext m; simp [map_add]
          map_smul' := fun r f => by
            apply Subtype.ext; simp only [SetLike.val_smul]; ext m; simp [map_smul] }
      map_add' := fun v₁ v₂ => by
        ext f : 1; exact Subtype.ext (by ext m; simp [TensorProduct.mk])
      map_smul' := fun r v => by
        ext f : 1
        exact Subtype.ext (by ext m; simp [TensorProduct.mk, TensorProduct.smul_tmul']) }


def leftInfChars
    (M : LieBimodule R 𝔤) :
    Set (↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :=
  { θ | ∃ (m : M.carrier), m ≠ 0 ∧
    ∀ (z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)),
      M.leftAction (z : UniversalEnvelopingAlgebra R 𝔤) m = θ z • m }


def infCharsOfModule
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] :
    Set (↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :=
  { χ | ∃ (act : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M),
    (∀ (x : 𝔤) (m : M), act (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆) ∧
    ∃ (m : M), m ≠ 0 ∧
      ∀ (z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)),
        act (z : UniversalEnvelopingAlgebra R 𝔤) m = χ z • m }

def IsDominantIntegralWeight (Δ : TriangularDecomposition R 𝔤)
    (_rd : PositiveRootData Δ) (chev : ChevalleyData Δ) (γ : Δ.𝔥 →ₗ[R] R) : Prop :=
  chev.IsDominantIntegral γ

end
