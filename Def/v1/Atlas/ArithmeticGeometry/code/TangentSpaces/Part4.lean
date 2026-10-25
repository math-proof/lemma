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
import Instance.v1.Atlas.ArithmeticGeometry.code.TangentSpaces.Part2


noncomputable section

open Matrix Module Submodule LinearMap FiniteDimensional MvPolynomial

section GeometricTangentSpace

variable {k : Type*} [Field k] {n : ℕ}

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

end SingularLocus
end GeometricTangentSpace
end
