/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.FunctionFieldGenerators
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.ProductVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ProductVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.CotangentLocal
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.RegularFunctions
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.CotangentLocal
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.RegularFunctions

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

theorem coordinateRingBar_isDomain' (k : Type*) [Field k] (N : ℕ)
    (V : Set (AffineSpace_k k N)) (hV : IsAffineVariety k N V) :
    IsDomain (AffineCoordinateRingBar V) :=
  coordinateRingBar_isDomain k hV

def functionField (k : Type*) [Field k] (N : ℕ)
    (V : Set (AffineSpace_k k N)) (hV : IsAffineVariety k N V) : Type _ :=
  letI : IsDomain (AffineCoordinateRingBar V) := coordinateRingBar_isDomain' k N V hV

  FractionRing (AffineCoordinateRingBar V)

@[reducible] noncomputable def functionField.instField (k : Type*) [Field k] (N : ℕ)
    (V : Set (AffineSpace_k k N)) (hV : IsAffineVariety k N V) :
    Field (functionField k N V hV) := by
  unfold functionField
  letI : IsDomain (AffineCoordinateRingBar V) := coordinateRingBar_isDomain' k N V hV
  exact FractionRing.field (AffineCoordinateRingBar V)

noncomputable instance (k : Type*) [Field k] (N : ℕ)
    (V : Set (AffineSpace_k k N)) (hV : IsAffineVariety k N V) :
    Field (functionField k N V hV) := functionField.instField k N V hV

@[reducible] noncomputable def functionField.instAlgebra (k : Type*) [Field k] (N : ℕ)
    (V : Set (AffineSpace_k k N)) (hV : IsAffineVariety k N V) :
    Algebra (AlgebraicClosure k) (functionField k N V hV) := by
  letI : IsDomain (MvPolynomial (Fin N) (AlgebraicClosure k) ⧸ idealOfAlgebraicSet V) :=
    coordinateRingBar_isDomain' k N V hV
  show Algebra (AlgebraicClosure k) (FractionRing (MvPolynomial (Fin N) (AlgebraicClosure k) ⧸ idealOfAlgebraicSet V))
  infer_instance

noncomputable instance (k : Type*) [Field k] (N : ℕ)
    (V : Set (AffineSpace_k k N)) (hV : IsAffineVariety k N V) :
    Algebra (AlgebraicClosure k) (functionField k N V hV) := functionField.instAlgebra k N V hV

def HasDimension (k : Type*) [Field k] (N : ℕ)
    (V : Set (AffineSpace_k k N)) (d : ℕ) : Prop :=
  ∃ (hV : IsAffineVariety k N V),
    Algebra.trdeg (AlgebraicClosure k) (functionField k N V hV) = d

def affinePartOfProjective (k : Type*) [Field k] {n : ℕ}
    (V : Set (ℙ (AlgebraicClosure k) (Fin (n + 1) → AlgebraicClosure k)))
    (i : Fin (n + 1)) : Set (Fin n → AlgebraicClosure k) :=
  (affinePatchEquiv (AlgebraicClosure k) i) '' {p : affinePatch (AlgebraicClosure k) i | ↑p ∈ V}

def IsProjectiveHypersurface (k : Type*) [Field k] {n : ℕ}
    (V : Set (ℙ (AlgebraicClosure k) (Fin (n + 1) → AlgebraicClosure k))) : Prop :=
  IsProjectiveVariety (AlgebraicClosure k) V ∧
    ∃ F : MvPolynomial (Fin (n + 1)) (AlgebraicClosure k),
      Irreducible F ∧ (∃ d, F.IsHomogeneous d) ∧
      V = ProjectiveAlgebraicSet (AlgebraicClosure k) {F}

def HasProjectiveDimension (k : Type*) [Field k] {n : ℕ}
    (V : Set (ℙ (AlgebraicClosure k) (Fin (n + 1) → AlgebraicClosure k))) (d : ℕ) : Prop :=
  IsProjectiveVariety (AlgebraicClosure k) V ∧
    ∃ (i : Fin (n + 1)),
      HasDimension k n (affinePartOfProjective k V i) d

namespace SingularLocus

variable (k : Type*) [Field k]

open MvPolynomial Matrix

def jacobianPolyMatrix (n m : ℕ)
    (f : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k)) :
    Matrix (Fin m) (Fin n) (MvPolynomial (Fin n) (AlgebraicClosure k)) :=
  Matrix.of fun i j => (MvPolynomial.pderiv j) (f i)

def minorDetPolys (n m r : ℕ)
    (M : Matrix (Fin m) (Fin n) (MvPolynomial (Fin n) (AlgebraicClosure k))) :
    Set (MvPolynomial (Fin n) (AlgebraicClosure k)) :=
  { d | ∃ (ri : Fin r → Fin m) (ci : Fin r → Fin n),
    d = (M.submatrix ri ci).det }

def singularLocusIntrinsic (n m r : ℕ)
    (f : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k)) :
    Set (AffineSpace_k k n) :=
  { P | P ∈ AlgebraicSet k n (Set.range f) ∧
        (TangentSpaces.jacobianMatrix n m f P).rank < r }

def singularLocusPolys (n m r : ℕ)
    (f : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k)) :
    Set (MvPolynomial (Fin n) (AlgebraicClosure k)) :=
  Set.range f ∪ minorDetPolys k n m r (jacobianPolyMatrix k n m f)

def singularLocusAlgebraic (n m r : ℕ)
    (f : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k)) :
    Set (AffineSpace_k k n) :=
  AlgebraicSet k n (singularLocusPolys k n m r f)


def IsSmoothPoint (k : Type*) [Field k] (n m d : ℕ)
    (f : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k))
    (P : Fin n → AlgebraicClosure k) : Prop :=
  P ∈ AlgebraicSet k n (Set.range f) ∧
    Module.finrank (AlgebraicClosure k)
      (TangentSpaces.tangentSpace (TangentSpaces.jacobianMatrix n m f P)) = d
