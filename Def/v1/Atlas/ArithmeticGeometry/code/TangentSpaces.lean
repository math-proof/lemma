/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.FunctionFieldGenerators
import Def.v1.Atlas.ArithmeticGeometry.code.ProductVarieties.Part5
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ProductVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.CotangentLocal
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.RegularFunctions
import Def.v1.Atlas.ArithmeticGeometry.code.CotangentLocal.Part3
import Def.v1.Atlas.ArithmeticGeometry.code.RegularFunctions.Part9


noncomputable section

open Matrix Module Submodule LinearMap FiniteDimensional MvPolynomial

section GeometricTangentSpace

variable {k : Type*} [Field k] {n : ℕ}

def totalDerivativeAt (f : MvPolynomial (Fin n) k) (P : Fin n → k) (v : Fin n → k) : k :=
  ∑ i : Fin n, MvPolynomial.eval P (MvPolynomial.pderiv i f) * v i

def totalDerivativeAtLin (f : MvPolynomial (Fin n) k) (P : Fin n → k) :
    (Fin n → k) →ₗ[k] k where
  toFun v := totalDerivativeAt f P v
  map_add' a b := by
    simp only [totalDerivativeAt, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [totalDerivativeAt, Pi.smul_apply, smul_eq_mul, mul_left_comm,
      ← Finset.mul_sum, RingHom.id_apply]

def tangentSpacePoly (f : MvPolynomial (Fin n) k) (P : Fin n → k) :
    Submodule k (Fin n → k) :=
  LinearMap.ker (totalDerivativeAtLin f P)

def tangentSpaceIdeal (I : Ideal (MvPolynomial (Fin n) k)) (P : Fin n → k) :
    Submodule k (Fin n → k) :=
  ⨅ f ∈ I, tangentSpacePoly f P

def jointLinearizationMap {m : ℕ} (f : Fin m → MvPolynomial (Fin n) k) (P : Fin n → k) :
    (Fin n → k) →ₗ[k] (Fin m → k) where
  toFun v := fun i => totalDerivativeAtLin (f i) P v
  map_add' a b := by ext i; simp [totalDerivativeAtLin, map_add]
  map_smul' c v := by ext i; simp [totalDerivativeAtLin, map_smul]

def jacobianMatrix (n m : ℕ) (f : Fin m → MvPolynomial (Fin n) k)
    (P : Fin n → k) : Matrix (Fin m) (Fin n) k :=
  Matrix.of fun i j => MvPolynomial.eval P ((MvPolynomial.pderiv j) (f i))

def tangentSpace {m n : ℕ} (M : Matrix (Fin m) (Fin n) k) : Submodule k (Fin n → k) :=
  LinearMap.ker M.mulVecLin

def cotangentSpaceDual {m n : ℕ} (M : Matrix (Fin m) (Fin n) k) :
    Submodule k (Module.Dual k (Fin n → k)) :=
  (tangentSpace M).dualAnnihilator

def cotangentSpace {m n : ℕ} (M : Matrix (Fin m) (Fin n) k) : Submodule k (Fin m → k) :=
  LinearMap.range M.mulVecLin


open MvPolynomial in
def IsHypersurface (k : Type*) [Field k] (N : ℕ)
    (W : Set (AffineSpace_k k N)) : Prop :=
  IsAffineVariety k N W ∧
    (idealOfAlgebraicSet W).IsPrincipal ∧
    idealOfAlgebraicSet W ≠ ⊥

end GeometricTangentSpace
end
