/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HCBimoduleProjectives.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.LieGroups.code.MaximalQuotients
import Lemma.Int.Any_EqUeaAction
import Mathlib.Algebra.Lie.Semisimple.Defs
import Structure.v1.Atlas.LieGroups.code.HCBimoduleProjectives


noncomputable section

universe u_R u_𝔤 u_mod

variable {R : Type u_R} [CommRing R]

variable {𝔤 : Type u_𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]

def IsProjectiveInHCThetaOne (P : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (θ : CenterCharacter R 𝔤)
    (hP : IsInHCThetaOne P θ) : Prop :=
  ∀ (Y₁ Y₂ : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (hY₁ : IsInHCThetaOne Y₁ θ) (hY₂ : IsInHCThetaOne Y₂ θ)
    (g : HCThetaOneHom Y₁ Y₂ θ hY₁ hY₂) (f : HCThetaOneHom P Y₂ θ hP hY₂),
    Function.Surjective g.toLinearMap →
    ∃ (lift : HCThetaOneHom P Y₁ θ hP hY₁),
      ∀ m : P.carrier, g.toLinearMap (lift.toLinearMap m) = f.toLinearMap m

def IsTensorProductBimoduleWithUTheta
    {R : Type u_R} [CommRing R] {𝔤 : Type u_𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (P : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤) (θ : CenterCharacter R 𝔤)
    (V : Type*) [AddCommGroup V] [Module R V] : Prop :=
  ∃ (T : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤),

    (∃ (f : P.carrier →ₗ[R] T.carrier),
      Function.Bijective f ∧
      (∀ (u : UniversalEnvelopingAlgebra R 𝔤) (m : P.carrier),
        f (P.leftAction u m) = T.leftAction u (f m)) ∧
      (∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (m : P.carrier),
        f (P.rightAction u m) = T.rightAction u (f m))) ∧

    (∃ (ι : V →ₗ[R] T.carrier),
      ∀ t : T.carrier, ∃ (n : ℕ) (vs : Fin n → V)
        (us : Fin n → (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ),
        t = ∑ i, T.rightAction (us i) (ι (vs i))) ∧

    (∀ (z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
      (t : T.carrier),
      T.rightAction (MulOpposite.op (z : UniversalEnvelopingAlgebra R 𝔤)) t = θ z • t)

def LieBimodule.IsFiniteLengthBimodule (M : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤) : Prop :=
  ∃ n : ℕ, ∃ (chain : Fin (n + 1) → Submodule R M.carrier),
    chain ⟨0, Nat.zero_lt_succ n⟩ = ⊥ ∧
    chain ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ = ⊤ ∧

    (∀ i : Fin n,
      chain ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ <
        chain ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) ∧

    (∀ i : Fin n,
      M.IsSubBimodule (chain ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) ∧
    (∀ i : Fin n,
      M.IsSubBimodule (chain ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)) ∧


    (∀ i : Fin n, ∀ (W : Submodule R M.carrier), M.IsSubBimodule W →
      chain ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ≤ W →
      W ≤ chain ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ →
      W = chain ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ∨
      W = chain ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

def iteratedKerThetaRightAction (M : LieBimodule R 𝔤)
    (θ : CenterCharacter R 𝔤)
    (zs : List (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)))
    (m : M.carrier) : M.carrier :=
  zs.foldl (fun acc z =>
    let θz : R := θ z
    let zVal : UniversalEnvelopingAlgebra R 𝔤 := z
    let kerElem : UniversalEnvelopingAlgebra R 𝔤 := zVal - algebraMap R _ θz
    M.rightAction (MulOpposite.op kerElem) acc) m

end
