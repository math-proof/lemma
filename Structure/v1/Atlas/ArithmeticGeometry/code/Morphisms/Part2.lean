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
import Def.v1.Atlas.ArithmeticGeometry.code.Morphisms.Part3


noncomputable section

open MvPolynomial

variable (k : Type*) [Field k]

/-- **Definition 14.6.** An *affine isomorphism* $X \cong Y$ consists of mutually
inverse affine morphisms $X \to Y$ and $Y \to X$. -/
structure AffineIsomorphism {m n : ℕ}
    (X : Set (AffineSpace_k k m)) (Y : Set (AffineSpace_k k n)) where
  toMorphism : AffineMorphism k m n X Y
  invMorphism : AffineMorphism k n m Y X
  left_inv : ∀ Q ∈ Y, toMorphism.toFun k (invMorphism.toFun k Q) = Q
  right_inv : ∀ P ∈ X, invMorphism.toFun k (toMorphism.toFun k P) = P

end
