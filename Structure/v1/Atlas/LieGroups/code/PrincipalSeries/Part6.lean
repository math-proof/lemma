/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PrincipalSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.VermaModules.Part7
import Lemma.Int.WeightSubspace.eq.ToSubmoduleWeightSpace
import Lemma.Int.IsInQPlus0
import Def.v1.Atlas.LieGroups.code.CategoryO.Part3
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.Algebra.Lie.Submodule
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Def.v1.Atlas.LieGroups.code.PrincipalSeries.Part5


noncomputable section

universe u_mod

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

attribute [instance] PrincipalSeriesBimodule.M_source_acg
  PrincipalSeriesBimodule.M_source_mod PrincipalSeriesBimodule.M_source_lrm
  PrincipalSeriesBimodule.M_source_lm PrincipalSeriesBimodule.M_target_acg
  PrincipalSeriesBimodule.M_target_mod PrincipalSeriesBimodule.M_target_lrm
  PrincipalSeriesBimodule.M_target_lm

structure LieGroupData (Δ : TriangularDecomposition R 𝔤) where
  G_c : Type u_mod
  H_c : Type u_mod
  incl : H_c → G_c
  Ad : G_c → (𝔤 →ₗ[R] 𝔤)

structure SmoothSectionsFinite
    (Δ : TriangularDecomposition R 𝔤)
    (wt_lambda wt_mu : Δ.𝔥 →ₗ[R] R) where
  carrier : Type u_mod
  [carrier_acg : AddCommGroup carrier]
  [carrier_mod : Module R carrier]
  hc_structure : @PS_IsHarishChandraBimodule R _ 𝔤 _ _ carrier carrier_acg carrier_mod
  is_locally_finite : ∀ (f : carrier),
    (@Submodule.span R carrier _ carrier_acg.toAddCommMonoid carrier_mod
      (Set.range (fun x => hc_structure.left_action x f))).FG
  right_action_cartan_weight : ∀ (h : Δ.𝔥) (f : carrier),
    hc_structure.right_action (h : 𝔤) f =
      @SMul.smul R carrier
        carrier_mod.toDistribMulAction.toMulAction.toSMul
        (wt_mu h) f
  left_action_cartan_weight : ∀ (h : Δ.𝔥) (f : carrier),
    hc_structure.left_action (h : 𝔤) f =
      @SMul.smul R carrier
        carrier_mod.toDistribMulAction.toMulAction.toSMul
        (wt_lambda h) f

attribute [instance] SmoothSectionsFinite.carrier_acg SmoothSectionsFinite.carrier_mod

structure MatrixCoefficientMap
    {Δ : TriangularDecomposition R 𝔤}
    (P : PrincipalSeriesBimodule Δ)
    (C : SmoothSectionsFinite Δ P.wt_lambda P.wt_mu)
    (inst_acg : AddCommGroup P.carrierType)
    (inst_mod : @Module R P.carrierType _ inst_acg.toAddCommMonoid)
    (hcP : @PS_IsHarishChandraBimodule R _ 𝔤 _ _ P.carrierType inst_acg inst_mod) where
  toFun : P.carrierType → C.carrier
  map_add : ∀ (a b : P.carrierType),
    toFun (@HAdd.hAdd P.carrierType P.carrierType P.carrierType
      (@instHAdd P.carrierType inst_acg.toAddGroup.toAdd) a b) =
      toFun a + toFun b
  map_smul : ∀ (r : R) (a : P.carrierType),
    toFun (@SMul.smul R P.carrierType
      inst_mod.toDistribMulAction.toMulAction.toSMul r a) =
      r • toFun a
  injective : Function.Injective toFun
  surjective : Function.Surjective toFun
  left_compat : ∀ (x : 𝔤) (f : P.carrierType),
    toFun (hcP.left_action x f) = C.hc_structure.left_action x (toFun f)
  right_compat : ∀ (x : 𝔤) (f : P.carrierType),
    toFun (hcP.right_action x f) = C.hc_structure.right_action x (toFun f)

structure LieGroupRepresentation
    {Δ : TriangularDecomposition R 𝔤}
    (G_data : LieGroupData Δ)
    (V : Type u_mod) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V] where
  π : G_data.G_c → (V →ₗ[R] V)
  π_inv : G_data.G_c → (V →ₗ[R] V)
  π_inv_left : ∀ (g : G_data.G_c) (v : V), π_inv g (π g v) = v
  π_inv_right : ∀ (g : G_data.G_c) (v : V), π g (π_inv g v) = v

structure SmoothSectionsEval
    {Δ : TriangularDecomposition R 𝔤}
    {wt_lambda wt_mu : Δ.𝔥 →ₗ[R] R}
    (C : SmoothSectionsFinite Δ wt_lambda wt_mu)
    (G_data : LieGroupData Δ) where
  eval : C.carrier → G_data.G_c → R
  eval_linear : ∀ (r : R) (f₁ f₂ : C.carrier) (g : G_data.G_c),
    eval (r • f₁ + f₂) g = r * eval f₁ g + eval f₂ g
  eval_injective : ∀ (f₁ f₂ : C.carrier),
    (∀ g, eval f₁ g = eval f₂ g) → f₁ = f₂

structure FunctorHLambda
    (Δ : TriangularDecomposition R 𝔤)
    (wt_lambda : Δ.𝔥 →ₗ[R] R) where
  M_lambda : Type u_mod
  [M_lambda_acg : AddCommGroup M_lambda]
  [M_lambda_mod : Module R M_lambda]
  [M_lambda_lrm : LieRingModule 𝔤 M_lambda]
  [M_lambda_lm : LieModule R 𝔤 M_lambda]
  verma_lambda : IsVermaModule Δ M_lambda wt_lambda

end
