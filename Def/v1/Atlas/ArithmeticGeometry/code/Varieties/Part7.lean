/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part5
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.AffineVarieties
import Mathlib.Topology.Basic
import Mathlib.Topology.Order
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Structure.v1.Atlas.ArithmeticGeometry.code.Varieties
variable (k : Type*) [Field k]


/-- The underlying set-theoretic map of an affine morphism. -/
def AffineMorphism.toFun {m n : ℕ} {X : Set (AffineSpace_k k m)}
    {Y : Set (AffineSpace_k k n)} (φ : AffineMorphism k m n X Y)
    (P : AffineSpace_k k m) : AffineSpace_k k n :=
  polyMapEval k m n φ.polys P

/-- The identity affine morphism on $X$, given by the coordinate polynomials $X_1, \ldots, X_n$. -/
def AffineMorphism.id {n : ℕ} (X : Set (AffineSpace_k k n)) :
    AffineMorphism k n n X X where
  polys := fun i => MvPolynomial.X i
  maps_to := by
    intro P hP
    have : polyMapEval k n n (fun i => MvPolynomial.X i) P = P := by
      ext j; simp [polyMapEval, MvPolynomial.eval_X]
    rw [this]; exact hP

/-- Composition of affine morphisms $g \circ f : X \to Z$. -/
def AffineMorphism.comp {m n r : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    {Z : Set (AffineSpace_k k r)}
    (g : AffineMorphism k n r Y Z) (f : AffineMorphism k m n X Y) :
    AffineMorphism k m r X Z where
  polys := fun j => MvPolynomial.bind₁ f.polys (g.polys j)
  maps_to := by
    intro P hP
    rw [polyMapEval_bind₁]
    exact g.maps_to _ (f.maps_to P hP)

