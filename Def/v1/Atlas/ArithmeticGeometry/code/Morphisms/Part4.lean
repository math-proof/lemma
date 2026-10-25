/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Morphisms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part7
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Varieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.VarietyAlgebraEquiv
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Theorem1324
import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part9
import Theorem.v1.Atlas.ArithmeticGeometry.code.VarietyAlgebraEquiv.Part2
import Theorem.v1.Atlas.ArithmeticGeometry.code.Theorem1324
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Basic
import Mathlib.Topology.Order
import Structure.v1.Atlas.ArithmeticGeometry.code.Morphisms.Part2


noncomputable section

open MvPolynomial

variable (k : Type*) [Field k]

/-- Two algebraic subsets $X$ and $Y$ are *isomorphic as affine varieties* if
there exists an affine isomorphism between them. -/
def AreIsomorphic {m n : ℕ}
    (X : Set (AffineSpace_k k m)) (Y : Set (AffineSpace_k k n)) : Prop :=
  Nonempty (AffineIsomorphism k X Y)

/-- An affine morphism $f$ is an *isomorphism* iff it admits an affine inverse
$g$ in the morphism sense (mutually inverse on the underlying point sets). -/
def AffineMorphism.IsIsomorphism {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (f : AffineMorphism k m n X Y) : Prop :=
  ∃ g : AffineMorphism k n m Y X,
    (∀ Q ∈ Y, f.toFun k (g.toFun k Q) = Q) ∧
    (∀ P ∈ X, g.toFun k (f.toFun k P) = P)


/-- Reflexivity for the isomorphism relation: the identity morphism realises
$X \cong X$. -/
def AffineIsomorphism.refl {n : ℕ} (X : Set (AffineSpace_k k n)) :
    AffineIsomorphism k X X where
  toMorphism := AffineMorphism.id k X
  invMorphism := AffineMorphism.id k X
  left_inv Q _ := by simp [AffineMorphism.toFun_id]
  right_inv P _ := by simp [AffineMorphism.toFun_id]

/-- Symmetry: an isomorphism $X \cong Y$ inverts to an isomorphism $Y \cong X$. -/
def AffineIsomorphism.symm {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (φ : AffineIsomorphism k X Y) : AffineIsomorphism k Y X where
  toMorphism := φ.invMorphism
  invMorphism := φ.toMorphism
  left_inv := φ.right_inv
  right_inv := φ.left_inv

/-- Transitivity: composition of two affine isomorphisms is an affine
isomorphism. -/
def AffineIsomorphism.trans {m n r : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    {Z : Set (AffineSpace_k k r)}
    (φ : AffineIsomorphism k X Y) (ψ : AffineIsomorphism k Y Z) :
    AffineIsomorphism k X Z where
  toMorphism := ψ.toMorphism.comp k φ.toMorphism
  invMorphism := φ.invMorphism.comp k ψ.invMorphism
  left_inv Q hQ := by
    have h1 : (ψ.toMorphism.comp k φ.toMorphism).toFun k
        ((φ.invMorphism.comp k ψ.invMorphism).toFun k Q)
        = ψ.toMorphism.toFun k (φ.toMorphism.toFun k
            (φ.invMorphism.toFun k (ψ.invMorphism.toFun k Q))) := by
      simp only [AffineMorphism.toFun_comp]
    have h2 : ψ.invMorphism.toFun k Q ∈ Y := ψ.invMorphism.maps_to Q hQ
    rw [h1, φ.left_inv _ h2, ψ.left_inv _ hQ]
  right_inv P hP := by
    have h1 : (φ.invMorphism.comp k ψ.invMorphism).toFun k
        ((ψ.toMorphism.comp k φ.toMorphism).toFun k P)
        = φ.invMorphism.toFun k (ψ.invMorphism.toFun k
            (ψ.toMorphism.toFun k (φ.toMorphism.toFun k P))) := by
      simp only [AffineMorphism.toFun_comp]
    have h2 : φ.toMorphism.toFun k P ∈ Y := φ.toMorphism.maps_to P hP
    rw [h1, ψ.right_inv _ h2, φ.right_inv _ hP]


end
