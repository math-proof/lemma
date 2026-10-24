/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/Prop194Audit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.PrincipalSeries
import Lemma.Int.GetLift_ToEndSubMulS.eq.Zero.of.All_EqGetLiftSMul


example (R : Type*) [CommRing R] (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (P : PrincipalSeriesBimodule Δ)
    (inst_acg : AddCommGroup P.carrierType)
    (inst_mod : @Module R P.carrierType _ inst_acg.toAddCommMonoid)
    (hcP : @PS_IsHarishChandraBimodule R _ 𝔤 _ _ P.carrierType inst_acg inst_mod)
    (roots : @PS_PositiveRootData R _ 𝔤 _ _ Δ)
    (V : Type*) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V] [Module.Finite R V]
    (Φ_V : PhiMap P V)
    (Φ_gV : PhiMap P (TensorProduct R 𝔤 V))
    (wt_lambda_ext : 𝔤 →ₗ[R] R)
    (hwt_compat : ∀ (h : Δ.𝔥), wt_lambda_ext (h : 𝔤) = P.wt_lambda h)
    (hwt_npos_zero : ∀ (e : Δ.𝔫_pos), wt_lambda_ext (e : 𝔤) = 0)
    (hwt_nneg_zero : ∀ (f : Δ.𝔫_neg), wt_lambda_ext (f : 𝔤) = 0) :
    ∀ (v : V) (ℓ : V →ₗ[R] R) (b : 𝔤),
      hcP.right_action b (Φ_V.phi v ℓ) =
        Φ_gV.phi (b ⊗ₜ[R] v)
          (concreteTensorDual wt_lambda_ext ℓ +
           Finset.univ.sum (fun (α : Fin roots.n_roots) =>
            concreteTensorDual (roots.f_root_star α)
              (contragredientAction (roots.f_root α) ℓ))) :=
  principalSeries_right_action P inst_acg inst_mod hcP roots V Φ_V
    Φ_gV wt_lambda_ext hwt_compat hwt_npos_zero hwt_nneg_zero
