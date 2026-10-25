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
import Abbrev.v1.Atlas.LieGroups.code.MaximalQuotients


noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

attribute [instance] LieBimodule.instAddCommGroup LieBimodule.instModule

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

end
