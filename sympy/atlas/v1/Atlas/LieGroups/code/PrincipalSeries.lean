/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PrincipalSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.VermaModules
import Lemma.Int.WeightSubspace.eq.ToSubmoduleWeightSpace
import Lemma.Int.IsInQPlus0
import sympy.atlas.v1.Atlas.LieGroups.code.CategoryO
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.Algebra.Lie.Submodule
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.RingTheory.Finiteness.Basic

noncomputable section

universe u_mod

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

structure PS_IsHarishChandraBimodule
    (M : Type*) [AddCommGroup M] [Module R M] where
  left_action : 𝔤 →ₗ⁅R⁆ Module.End R M
  right_action : 𝔤 →ₗ⁅R⁆ Module.End R M
  actions_comm : ∀ (x y : 𝔤) (m : M),
    left_action x (right_action y m) = right_action y (left_action x m)
  locally_finite_diag : ∀ m : M,
    (Submodule.span R (Set.range (fun x => left_action x m - right_action x m))).FG

def IsLocallyFiniteMap
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) : Prop :=
  (LinearMap.range f).FG

def RestrictedDual
    (M : Type*) [AddCommGroup M] [Module R M] :
    Type _ :=
  { f : Module.Dual R M // ∃ (N : Submodule R M),
      N ≤ LinearMap.ker f ∧ (Submodule.map (Submodule.mkQ N) ⊤).FG }

def IsInRestrictedDual
    {M : Type*} [AddCommGroup M] [Module R M]
    (f : Module.Dual R M) : Prop :=
  ∃ (N : Submodule R M), N ≤ LinearMap.ker f ∧ (Submodule.map (Submodule.mkQ N) ⊤).FG

variable {R 𝔤}

abbrev liftAct (R : Type*) [CommRing R] (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (V : Type*) [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (x : UniversalEnvelopingAlgebra R 𝔤) (v : V) : V :=
  (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 V)) x v

structure PrincipalSeriesBimodule
    (Δ : TriangularDecomposition R 𝔤) where
  wt_lambda : Δ.𝔥 →ₗ[R] R
  wt_mu : Δ.𝔥 →ₗ[R] R
  M_source : Type u_mod
  [M_source_acg : AddCommGroup M_source]
  [M_source_mod : Module R M_source]
  [M_source_lrm : LieRingModule 𝔤 M_source]
  [M_source_lm : LieModule R 𝔤 M_source]
  verma_source : IsVermaModule Δ M_source wt_lambda
  M_target : Type u_mod
  [M_target_acg : AddCommGroup M_target]
  [M_target_mod : Module R M_target]
  [M_target_lrm : LieRingModule 𝔤 M_target]
  [M_target_lm : LieModule R 𝔤 M_target]
  verma_target : IsVermaModule Δ M_target wt_mu

attribute [instance] PrincipalSeriesBimodule.M_source_acg
  PrincipalSeriesBimodule.M_source_mod PrincipalSeriesBimodule.M_source_lrm
  PrincipalSeriesBimodule.M_source_lm PrincipalSeriesBimodule.M_target_acg
  PrincipalSeriesBimodule.M_target_mod PrincipalSeriesBimodule.M_target_lrm
  PrincipalSeriesBimodule.M_target_lm

def PrincipalSeriesBimodule.carrierType
    {Δ : TriangularDecomposition R 𝔤}
    (P : PrincipalSeriesBimodule Δ) : Type _ :=
  { f : P.M_source →ₗ[R] Module.Dual R P.M_target //
    IsLocallyFiniteMap R f ∧
    ∀ m : P.M_source, IsInRestrictedDual R (f m) }

structure HCBimoduleHom
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    (hcM : PS_IsHarishChandraBimodule R 𝔤 M)
    (hcN : PS_IsHarishChandraBimodule R 𝔤 N) where
  toLinearMap : M →ₗ[R] N
  left_compat : ∀ (x : 𝔤) (m : M),
    toLinearMap (hcM.left_action x m) = hcN.left_action x (toLinearMap m)
  right_compat : ∀ (x : 𝔤) (m : M),
    toLinearMap (hcM.right_action x m) = hcN.right_action x (toLinearMap m)

def BorelBimoduleHom
    {Δ : TriangularDecomposition R 𝔤}
    (P : PrincipalSeriesBimodule Δ)
    {X : Type*} [AddCommGroup X] [Module R X]
    (hX : PS_IsHarishChandraBimodule R 𝔤 X) : Type _ :=
  { φ : X →ₗ[R] R //
    (∀ (f : Δ.𝔫_neg) (x : X), φ (hX.left_action f x) = 0) ∧
    (∀ (e : Δ.𝔫_pos) (x : X), φ (hX.right_action e x) = 0) ∧
    (∀ (h : Δ.𝔥) (x : X), φ (hX.left_action h x) = P.wt_mu h * φ x) ∧
    (∀ (h : Δ.𝔥) (x : X), φ (hX.right_action h x) = P.wt_lambda h * φ x) }

def IntermediateBorelHom
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (P : PrincipalSeriesBimodule Δ)
    {X : Type*} [AddCommGroup X] [Module R X]
    (hX : PS_IsHarishChandraBimodule R 𝔤 X) : Type _ :=
  { φ : X →ₗ[R] R //

    (∀ (e : Δ.𝔫_pos) (x : X), φ (hX.right_action e x) = 0) ∧

    (∀ (h : Δ.𝔥) (x : X), φ (hX.right_action h x) = P.wt_lambda h * φ x) }

structure PS_PositiveRootData
    {Δ : TriangularDecomposition R 𝔤} where
  n_roots : ℕ
  f_root : Fin n_roots → 𝔤
  f_root_star : Fin n_roots → (𝔤 →ₗ[R] R)
  f_root_in_neg : ∀ i, f_root i ∈ Δ.𝔫_neg

def contragredientAction
    {V : Type*} [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (x : 𝔤) (ℓ : V →ₗ[R] R) : V →ₗ[R] R :=
  -ℓ ∘ₗ (LieModule.toEnd R 𝔤 V x)

structure PhiMap
    {Δ : TriangularDecomposition R 𝔤}
    (P : PrincipalSeriesBimodule Δ)
    (V : Type u_mod) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V] where
  phi : V → (V →ₗ[R] R) → P.carrierType

def concreteTensorDual
    {M : Type*} {N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] R) (ℓ : N →ₗ[R] R) : (TensorProduct R M N) →ₗ[R] R :=
  (TensorProduct.dualDistrib R M N) (f ⊗ₜ[R] ℓ)

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

attribute [instance] FunctorHLambda.M_lambda_acg FunctorHLambda.M_lambda_mod
  FunctorHLambda.M_lambda_lrm FunctorHLambda.M_lambda_lm

def FunctorHLambda.onObject
    {Δ : TriangularDecomposition R 𝔤}
    {wt_lambda : Δ.𝔥 →ₗ[R] R}
    (H : FunctorHLambda Δ wt_lambda)
    (X : Type u_mod) [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X] : Type _ :=
  { f : H.M_lambda →ₗ⁅R, 𝔤⁆ X // IsLocallyFiniteMap R (f : H.M_lambda →ₗ[R] X) }

def FunctorHLambda.onMorphism
    {Δ : TriangularDecomposition R 𝔤}
    {wt_lambda : Δ.𝔥 →ₗ[R] R}
    (H : FunctorHLambda Δ wt_lambda)
    {X Y : Type u_mod} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    [AddCommGroup Y] [Module R Y]
    [LieRingModule 𝔤 Y] [LieModule R 𝔤 Y]
    (φ : X →ₗ⁅R, 𝔤⁆ Y)
    (hx : H.onObject X) : H.onObject Y :=
  ⟨φ.comp hx.val,


   by
    have hfg : (LinearMap.range (hx.val : H.M_lambda →ₗ[R] X)).FG := hx.property
    change (LinearMap.range (LieModuleHom.toLinearMap (φ.comp hx.val))).FG
    rw [LieModuleHom.toLinearMap_comp, LinearMap.range_comp]
    exact hfg.map _⟩

set_option linter.unusedVariables false in

def IsDominantWeight
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wt : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ α ∈ rd.posRoots, ∃ (n : ℕ), rd.corootPairing wt α = (n : R)
