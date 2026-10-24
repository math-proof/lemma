/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.GroupTheory.QuotientGroup.Basic

open LinearMap (BilinMap BilinForm)

noncomputable instance instInvertibleTwoOfNeZero (k : Type*) [Field k] [NeZero (2 : k)] :
    Invertible (2 : k) :=
  invertibleOfNonzero (NeZero.ne 2)

namespace QuadraticFormEquiv

section BasicProperties

variable {k : Type*} [CommSemiring k]
variable {V : Type*} [AddCommMonoid V] [Module k V]


end BasicProperties

section BilinQuadEquiv

variable {k : Type*} [Field k] [NeZero (2 : k)]
variable {V : Type*} [AddCommGroup V] [Module k V]

noncomputable def matrixBilinEquiv :
    Matrix n n k ≃ₗ[k] BilinMap k (n → k) k :=
  Matrix.toLinearMap₂' k

noncomputable def bilinFormToMatrix :
    BilinMap k (n → k) k ≃ₗ[k] Matrix n n k :=
  LinearMap.toMatrix₂' k

noncomputable def matrixToQuadraticForm (A : Matrix n n k) : QuadraticForm k (n → k) :=
  A.toQuadraticMap'

noncomputable def quadraticFormToMatrix (Q : QuadraticForm k (n → k)) : Matrix n n k :=
  Q.toMatrix'

def Represents {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (Q : QuadraticForm R M) (a : R) : Prop :=
  ∃ v : M, v ≠ 0 ∧ Q v = a

noncomputable def quadraticFormRank (Q : QuadraticForm k (n → k)) : ℕ :=
  Q.toMatrix'.rank

def quadraticFormIsNondegenerate (Q : QuadraticForm k (n → k)) : Prop :=
  quadraticFormRank Q = Fintype.card n

noncomputable def sqMonoidHom : kˣ →* kˣ where
  toFun u := u ^ 2
  map_one' := one_pow 2
  map_mul' a b := mul_pow a b 2

noncomputable def squaresSubgroup : Subgroup kˣ := (sqMonoidHom k).range

def SquareClassGroup := kˣ ⧸ squaresSubgroup k

instance squaresSubgroupNormal : (squaresSubgroup k).Normal := Subgroup.normal_of_comm _

noncomputable def toSquareClass : kˣ → SquareClassGroup k := QuotientGroup.mk

noncomputable def discrUnit (Q : QuadraticMap k (n → k) k) (hQ : Q.discr ≠ 0) : kˣ :=
  Units.mk0 Q.discr hQ

noncomputable def discriminant (Q : QuadraticMap k (n → k) k) (hQ : Q.discr ≠ 0) :
    SquareClassGroup k :=
  toSquareClass k (discrUnit k Q hQ)
