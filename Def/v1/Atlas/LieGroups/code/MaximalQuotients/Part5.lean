/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MaximalQuotients.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.LieGroups.code.HarishChandraIsomorphism.Part2
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Lie.OfAssociative
import Theorem.v1.Atlas.LieGroups.code.MaximalQuotients


noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

attribute [instance] LieBimodule.instAddCommGroup LieBimodule.instModule

def tensorBimodule
    (V : LieBimodule R 𝔤)
    (χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :
    LieBimodule R 𝔤 := by
  let bimodM := MaximalQuotient.bimodule χ
  let rTA := Module.End.rTensorAlgHom R V.carrier bimodM.carrier
  let lTA := Module.End.lTensorAlgHom R bimodM.carrier V.carrier

  have h_cross : ∀ (f : Module.End R V.carrier) (g : Module.End R bimodM.carrier),
      rTA f * lTA g = lTA g * rTA f := by
    intro f g; apply LinearMap.ext; intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v m =>
      change (rTA f) ((lTA g) (v ⊗ₜ[R] m)) = (lTA g) ((rTA f) (v ⊗ₜ[R] m))
      dsimp only [rTA, lTA]
      simp only [Module.End.rTensorAlgHom_apply_apply, Module.End.lTensorAlgHom_apply_apply]
      simp [TensorProduct.liftAux_tmul, LinearMap.compl₂_apply, TensorProduct.mk_apply]
    | add x y hx hy => simp [map_add, hx, hy]

  let diagLieHom : 𝔤 →ₗ⁅R⁆ Module.End R (TensorProduct R V.carrier bimodM.carrier) :=
  { toFun := fun x =>
      rTA (V.leftAction (UniversalEnvelopingAlgebra.ι R x)) +
      lTA (bimodM.leftAction (UniversalEnvelopingAlgebra.ι R x))
    map_add' := fun x y => by simp only [map_add]; abel
    map_smul' := fun c x => by
      simp only [map_smul, RingHom.id_apply, smul_add]
    map_lie' := fun {x y} => by
      simp only [LieRing.of_associative_ring_bracket]


      rw [LieHom.map_lie, LieRing.of_associative_ring_bracket]
      simp only [map_sub, map_mul]


      have hc1 := h_cross (V.leftAction (UniversalEnvelopingAlgebra.ι R x))
        (bimodM.leftAction (UniversalEnvelopingAlgebra.ι R y))
      have hc2 := h_cross (V.leftAction (UniversalEnvelopingAlgebra.ι R y))
        (bimodM.leftAction (UniversalEnvelopingAlgebra.ι R x))

      simp only [add_mul, mul_add]

      rw [hc1, hc2]
      abel }

  let leftAction' := UniversalEnvelopingAlgebra.lift R diagLieHom
  let rightAction' := lTA.comp bimodM.rightAction
  exact
  { carrier := TensorProduct R V.carrier bimodM.carrier
    leftAction := leftAction'
    rightAction := rightAction'
    actions_commute := fun u v m => by


      let E_v := rightAction' v

      have h_gen : ∀ x, diagLieHom x * E_v = E_v * diagLieHom x := by
        intro x
        show (rTA (V.leftAction (UniversalEnvelopingAlgebra.ι R x)) +
              lTA (bimodM.leftAction (UniversalEnvelopingAlgebra.ι R x))) *
              (lTA (bimodM.rightAction v)) =
            (lTA (bimodM.rightAction v)) *
              (rTA (V.leftAction (UniversalEnvelopingAlgebra.ι R x)) +
              lTA (bimodM.leftAction (UniversalEnvelopingAlgebra.ι R x)))
        simp only [add_mul, mul_add]
        rw [h_cross (V.leftAction (UniversalEnvelopingAlgebra.ι R x)) (bimodM.rightAction v)]
        congr 1


        rw [← map_mul, ← map_mul]
        congr 1

        ext m'
        exact bimodM.actions_commute (UniversalEnvelopingAlgebra.ι R x) v m'

      have h_all := UniversalEnvelopingAlgebra.lift_centralizes diagLieHom E_v h_gen u


      exact congr_fun (congr_arg DFunLike.coe h_all) m }

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]

def LieBimodule.toLieRingModule' {R' : Type*} [CommRing R'] {𝔤' : Type*} [LieRing 𝔤']
    [LieAlgebra R' 𝔤'] (M : LieBimodule R' 𝔤') :
    LieRingModule 𝔤' M.carrier where
  bracket x m := M.adjointAction x m
  add_lie x y m := by
    simp only [LieBimodule.adjointAction]
    simp only [map_add, MulOpposite.op_add, LinearMap.add_apply, LinearMap.sub_apply]
    abel
  lie_add x m n := by
    simp only [LieBimodule.adjointAction]
    simp only [map_add]
  leibniz_lie x y m := by
    simp only [LieBimodule.adjointAction]
    have hcomm_xy : M.leftAction (UniversalEnvelopingAlgebra.ι R' x)
        (M.rightAction (MulOpposite.op (UniversalEnvelopingAlgebra.ι R' y)) m) =
      M.rightAction (MulOpposite.op (UniversalEnvelopingAlgebra.ι R' y))
        (M.leftAction (UniversalEnvelopingAlgebra.ι R' x) m) :=
      M.actions_commute _ _ _
    have hcomm_yx : M.leftAction (UniversalEnvelopingAlgebra.ι R' y)
        (M.rightAction (MulOpposite.op (UniversalEnvelopingAlgebra.ι R' x)) m) =
      M.rightAction (MulOpposite.op (UniversalEnvelopingAlgebra.ι R' x))
        (M.leftAction (UniversalEnvelopingAlgebra.ι R' y) m) :=
      M.actions_commute _ _ _
    have hLmul : M.leftAction (UniversalEnvelopingAlgebra.ι R' x *
        UniversalEnvelopingAlgebra.ι R' y) m =
      M.leftAction (UniversalEnvelopingAlgebra.ι R' x)
        (M.leftAction (UniversalEnvelopingAlgebra.ι R' y) m) := by
      rw [map_mul]; rfl
    have hLmul' : M.leftAction (UniversalEnvelopingAlgebra.ι R' y *
        UniversalEnvelopingAlgebra.ι R' x) m =
      M.leftAction (UniversalEnvelopingAlgebra.ι R' y)
        (M.leftAction (UniversalEnvelopingAlgebra.ι R' x) m) := by
      rw [map_mul]; rfl
    have hRmul : M.rightAction (MulOpposite.op (UniversalEnvelopingAlgebra.ι R' y *
        UniversalEnvelopingAlgebra.ι R' x)) m =
      M.rightAction (MulOpposite.op (UniversalEnvelopingAlgebra.ι R' x))
        (M.rightAction (MulOpposite.op (UniversalEnvelopingAlgebra.ι R' y)) m) := by
      rw [MulOpposite.op_mul, map_mul]; rfl
    have hRmul' : M.rightAction (MulOpposite.op (UniversalEnvelopingAlgebra.ι R' x *
        UniversalEnvelopingAlgebra.ι R' y)) m =
      M.rightAction (MulOpposite.op (UniversalEnvelopingAlgebra.ι R' y))
        (M.rightAction (MulOpposite.op (UniversalEnvelopingAlgebra.ι R' x)) m) := by
      rw [MulOpposite.op_mul, map_mul]; rfl
    have hι_lie : UniversalEnvelopingAlgebra.ι R' ⁅x, y⁆ =
      UniversalEnvelopingAlgebra.ι R' x * UniversalEnvelopingAlgebra.ι R' y -
      UniversalEnvelopingAlgebra.ι R' y * UniversalEnvelopingAlgebra.ι R' x := by
      rw [(UniversalEnvelopingAlgebra.ι R').map_lie, LieRing.of_associative_ring_bracket]
    simp only [LinearMap.sub_apply]
    rw [hι_lie]
    simp only [map_sub, MulOpposite.op_sub, LinearMap.sub_apply]
    rw [hLmul, hLmul', hRmul, hRmul']
    rw [hcomm_xy, hcomm_yx]
    abel

@[reducible]
def LieBimodule.toLieModule' {R' : Type*} [CommRing R'] {𝔤' : Type*} [LieRing 𝔤']
    [LieAlgebra R' 𝔤'] (M : LieBimodule R' 𝔤') :
    @LieModule R' 𝔤' M.carrier _ _ _ M.instAddCommGroup M.instModule M.toLieRingModule' :=
  @LieModule.mk R' 𝔤' M.carrier _ _ _ M.instAddCommGroup M.instModule M.toLieRingModule'
    (fun t x m => by
      show M.adjointAction (t • x) m = t • M.adjointAction x m
      simp only [LieBimodule.adjointAction]
      simp only [map_smul, MulOpposite.op_smul, LinearMap.smul_apply, LinearMap.sub_apply]
      rw [smul_sub])
    (fun t x m => by
      show M.adjointAction x (t • m) = t • M.adjointAction x m
      simp only [LieBimodule.adjointAction, LinearMap.sub_apply, map_smul])

def UniversalEnvelopingAlgebra.counit {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤] :
    UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] R :=
  UniversalEnvelopingAlgebra.lift R (0 : 𝔤 →ₗ⁅R⁆ R)

def UniversalEnvelopingAlgebra.counitOp {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤] :
    (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ →ₐ[R] R where
  toFun x := UniversalEnvelopingAlgebra.counit x.unop
  map_one' := by simp [map_one]
  map_mul' a b := by simp [MulOpposite.unop_mul, map_mul, mul_comm]
  map_zero' := by simp [map_zero]
  map_add' a b := by simp [map_add]
  commutes' r := by
    simp only [MulOpposite.algebraMap_apply, MulOpposite.unop_op,
      UniversalEnvelopingAlgebra.counit, UniversalEnvelopingAlgebra.lift]
    simp [Algebra.algebraMap_eq_smul_one, map_smul, map_one]

def LieBimodule.trivial {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (V : Type*) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V] :
    LieBimodule R 𝔤 where
  carrier := V
  leftAction := UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 V)
  rightAction := (Algebra.ofId R (Module.End R V)).comp
    UniversalEnvelopingAlgebra.counitOp
  actions_commute := by
    intro u v m
    simp only [AlgHom.comp_apply, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one]
    exact LinearMap.map_smul _ _ _

end
