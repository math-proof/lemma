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
import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part7
variable (k : Type*) [Field k]


/-- The identity morphism evaluates to the identity function. -/
theorem AffineMorphism.toFun_id {n : ℕ} {X : Set (AffineSpace_k k n)}
    (P : AffineSpace_k k n) :
    (AffineMorphism.id k X).toFun k P = P := by
  ext j; simp [toFun, AffineMorphism.id, polyMapEval, MvPolynomial.eval_X]

/-- The underlying function of the composite of two affine morphisms is the composite of their underlying functions. -/
theorem AffineMorphism.toFun_comp {m n r : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    {Z : Set (AffineSpace_k k r)}
    (g : AffineMorphism k n r Y Z) (f : AffineMorphism k m n X Y)
    (P : AffineSpace_k k m) :
    (g.comp k f).toFun k P = g.toFun k (f.toFun k P) := by
  simp only [toFun, comp]
  exact polyMapEval_bind₁ k P f.polys g.polys

