/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MaximalQuotients.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.HarishChandraIsomorphism
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Lie.OfAssociative

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {R 𝔤}

structure LieBimodule (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤] where
  carrier : Type*
  [instAddCommGroup : AddCommGroup carrier]
  [instModule : Module R carrier]
  leftAction : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R carrier
  rightAction : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ →ₐ[R] Module.End R carrier
  actions_commute : ∀ (u : UniversalEnvelopingAlgebra R 𝔤)
    (v : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (m : carrier),
    leftAction u (rightAction v m) = rightAction v (leftAction u m)

attribute [instance] LieBimodule.instAddCommGroup LieBimodule.instModule

def LieBimodule.adjointAction (M : LieBimodule R 𝔤) (x : 𝔤) :
    Module.End R M.carrier :=
  M.leftAction (UniversalEnvelopingAlgebra.ι R x) -
  M.rightAction (MulOpposite.op (UniversalEnvelopingAlgebra.ι R x))

def LieBimodule.IsSubBimodule (M : LieBimodule R 𝔤) (S : Submodule R M.carrier) : Prop :=
  (∀ (u : UniversalEnvelopingAlgebra R 𝔤) (s : M.carrier), s ∈ S → M.leftAction u s ∈ S) ∧
  (∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (s : M.carrier), s ∈ S → M.rightAction u s ∈ S)

def LieBimodule.IsIrreducible (M : LieBimodule R 𝔤) : Prop :=
  (∃ m : M.carrier, m ≠ 0) ∧
  ∀ (S : Submodule R M.carrier), M.IsSubBimodule S → S = ⊥ ∨ S = ⊤

structure IsHarishChandraBimodule (M : LieBimodule R 𝔤) : Prop where
  locally_finite : ∀ (m : M.carrier), ∃ (S : Submodule R M.carrier),
    Module.Finite R S ∧ m ∈ S ∧
    ∀ (x : 𝔤), ∀ (s : M.carrier), s ∈ S → M.adjointAction x s ∈ S

structure LieBimodule.HasInfinitesimalCharacterPair (M : LieBimodule R 𝔤)
    (θ χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) : Prop where
  left_char : ∀ (z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
    (m : M.carrier),
    M.leftAction (z : UniversalEnvelopingAlgebra R 𝔤) m = θ z • m
  right_char : ∀ (z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
    (m : M.carrier),
    M.rightAction (MulOpposite.op (z : UniversalEnvelopingAlgebra R 𝔤)) m = χ z • m

def HomAdEquivariant
    (V : Type*) [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (M : LieBimodule R 𝔤) : Submodule R (V →ₗ[R] M.carrier) where
  carrier := { f | ∀ (x : 𝔤) (v : V), f ⁅x, v⁆ = M.adjointAction x (f v) }
  add_mem' := fun {f g} hf hg x v => by
    simp [LinearMap.add_apply, hf x v, hg x v, map_add]
  zero_mem' := fun x v => by simp
  smul_mem' := fun c {f} hf x v => by
    simp [LinearMap.smul_apply, hf x v, map_smul]

structure IsAdmissibleBimodule (M : LieBimodule R 𝔤) : Prop where
  isHC : IsHarishChandraBimodule M
  admissible : ∀ (V : Type 0) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V] [LieModule.IsIrreducible R 𝔤 V],
    Module.Finite R (HomAdEquivariant V M)

def maximalQuotientIdeal
    (χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :
    TwoSidedIdeal (UniversalEnvelopingAlgebra R 𝔤) :=
  TwoSidedIdeal.span
    { x | ∃ (z : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))),
      x = (z : UniversalEnvelopingAlgebra R 𝔤) - algebraMap R _ (χ z) }

abbrev MaximalQuotient
    (χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :=
  (maximalQuotientIdeal χ).ringCon.Quotient

noncomputable def MaximalQuotient.proj
    (χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :
    UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] MaximalQuotient χ := by
  sorry

def negOpLieHom : 𝔤 →ₗ⁅R⁆ (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ where
  toFun x := MulOpposite.op (-(UniversalEnvelopingAlgebra.ι R x))
  map_add' x y := by
    simp only [map_add, neg_add_rev, MulOpposite.op_add]; abel
  map_smul' c x := by
    simp only [map_smul, smul_neg, RingHom.id_apply, MulOpposite.op_neg, MulOpposite.op_smul]
  map_lie' {x y} := by
    simp only [LieRing.of_associative_ring_bracket, LieHom.map_lie]
    rw [← MulOpposite.op_mul, ← MulOpposite.op_mul, ← MulOpposite.op_sub]
    congr 1; simp only [neg_mul, mul_neg, neg_neg, neg_sub]

def ueaPrincipalAntiAut :
    UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ :=
  UniversalEnvelopingAlgebra.lift R negOpLieHom

def rmulAlgHom (A : Type*) [Ring A] [Algebra R A] :
    Aᵐᵒᵖ →ₐ[R] Module.End R A where
  toFun a :=
    { toFun := fun x => x * a.unop
      map_add' := fun x y => add_mul x y _
      map_smul' := fun c x => Algebra.smul_mul_assoc c x _ }
  map_one' := by ext; simp
  map_mul' a b := by ext x; simp [MulOpposite.unop_mul, mul_assoc]
  map_zero' := by ext; simp
  map_add' a b := by ext; simp [mul_add]
  commutes' r := by
    ext x; simp [Algebra.algebraMap_eq_smul_one, Algebra.mul_smul_comm]


def MaximalQuotient.bimodule
    (χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :
    LieBimodule R 𝔤 where
  carrier := MaximalQuotient χ
  leftAction := (Algebra.lmul R (MaximalQuotient χ)).comp (MaximalQuotient.proj χ)
  rightAction := (rmulAlgHom (MaximalQuotient χ)).comp (AlgHom.op (MaximalQuotient.proj χ))
  actions_commute := fun _ _ _ => (mul_assoc _ _ _).symm

theorem UniversalEnvelopingAlgebra.lift_centralizes
    {A : Type*} [Ring A] [Algebra R A]
    (f : 𝔤 →ₗ⁅R⁆ A) (E : A) (hf : ∀ x, f x * E = E * f x) :
    ∀ u, UniversalEnvelopingAlgebra.lift R f u * E =
      E * UniversalEnvelopingAlgebra.lift R f u := by
  let C := Subalgebra.centralizer R ({E} : Set A)
  have hfC : ∀ x, f x ∈ C := by
    intro x; rw [Subalgebra.mem_centralizer_iff]
    intro g hg; rw [Set.mem_singleton_iff.mp hg]; exact (hf x).symm
  let f' : 𝔤 →ₗ⁅R⁆ C :=
  { toFun := fun x => ⟨f x, hfC x⟩
    map_add' := fun x y => by ext; simp [map_add]
    map_smul' := fun c x => by ext; simp [map_smul]
    map_lie' := fun {x y} => by
      ext; simp only [LieHom.map_lie, LieRing.of_associative_ring_bracket]; rfl }
  let F' := UniversalEnvelopingAlgebra.lift R f'
  have key : C.val.comp F' = UniversalEnvelopingAlgebra.lift R f := by
    apply UniversalEnvelopingAlgebra.hom_ext R; ext x; simp [f', F']
  intro u
  have hu : UniversalEnvelopingAlgebra.lift R f u ∈ C := by rw [← key]; exact (F' u).2
  rw [Subalgebra.mem_centralizer_iff] at hu
  exact (hu E (Set.mem_singleton E)).symm


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

instance LieBimodule.trivial_finiteDimensional {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (V : Type*) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V] :
    Module.Finite R (LieBimodule.trivial V : LieBimodule R 𝔤).carrier :=
  ‹Module.Finite R V›
