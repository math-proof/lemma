/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.RingTheory.Coalgebra.TensorProduct
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Def.v1.Atlas.TensorCategories.code.HopfAlgebra.Part2
public import Theorem.v1.Atlas.TensorCategories.code.HopfAlgebra.Part2

@[expose] public section
set_option maxHeartbeats 800000

open Coalgebra HopfAlgebra WithConv LinearMap
open scoped TensorProduct

universe u v


section AntipodeSq

noncomputable section

section AntipodeComm

variable {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [HopfAlgebra R A]

/-- On a commutative Hopf algebra, the antipode promoted to an algebra homomorphism `A →ₐ[R] A`. -/
def HopfAlgebra.antipodeAlgHom : A →ₐ[R] A :=
  { antipode R with
    toFun := antipode R
    map_one' := HopfAlgebra.antipode_one
    map_mul' := HopfAlgebra.antipode_mul_comm
    map_zero' := map_zero _
    commutes' := fun r => by
      simp [Algebra.algebraMap_eq_smul_one, map_smul, HopfAlgebra.antipode_one] }

/-- Sigma-notation representative of `Δ(a * b)` obtained by multiplying termwise the
representatives of `Δ(a)` and `Δ(b)`. -/
def Coalgebra.Repr.mulRepr {a b : A} {ι κ : Type*} (ra : Coalgebra.Repr R a ι) (rb : Coalgebra.Repr R b κ) :
    Coalgebra.Repr R (a * b) (ι × κ) where
  index := ra.index ×ˢ rb.index
  left := fun ⟨i, j⟩ => ra.left i * rb.left j
  right := fun ⟨i, j⟩ => ra.right i * rb.right j
  eq := by
    rw [Bialgebra.comul_mul, ← ra.eq, ← rb.eq, Finset.sum_mul, Finset.sum_product]
    congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j
    exact (Algebra.TensorProduct.tmul_mul_tmul _ _ _ _).symm

/-- The "antimultiplication" map `A ⊗ A → A` in the general (possibly noncommutative) case,
defined as `μ ∘ τ ∘ (S ⊗ S)` where `τ` is the tensor swap. Sends `a ⊗ b` to `S(b) S(a)`. -/
def HopfAlgebra.antimul : A ⊗[R] A →ₗ[R] A :=
  (mul' R A).comp ((TensorProduct.comm R A A).toLinearMap.comp
    (TensorProduct.map (antipode R) (antipode R)))

end AntipodeComm

section DualAction

variable {k : Type u} [CommSemiring k] {H : Type v} [Semiring H] [Algebra k H] [HopfAlgebra k H]
variable {V : Type v} [AddCommGroup V] [Module k V] [Module H V] [SMulCommClass k H V]

/-- The `k`-linear map on `V` given by scalar multiplication by an element `h : H` (used to
build the right-dual `H`-action on `V^*`). -/
noncomputable def HopfAlgebra.rightDualSMulMap (h : H) : V →ₗ[k] V where
  toFun v := h • v
  map_add' := smul_add h
  map_smul' r v := by
    dsimp
    haveI : SMulCommClass H k V := SMulCommClass.symm k H V
    rw [smul_comm]

/-- The right-dual `H`-action on the linear dual `V^*` coming from a Hopf algebra `H`:
`(a · f)(v) = f(S(a) · v)`. -/
noncomputable def HopfAlgebra.rightDualAction (a : H) (f : Module.Dual k V) : Module.Dual k V :=
  f.comp (HopfAlgebra.rightDualSMulMap (k := k) (HopfAlgebra.antipode k a))

end DualAction
end
end AntipodeSq
