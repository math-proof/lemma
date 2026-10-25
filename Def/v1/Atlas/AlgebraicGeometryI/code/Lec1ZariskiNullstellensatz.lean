/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec1ZariskiNullstellensatz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
open MvPolynomial AlgebraicGeometry CategoryTheory


namespace Lec1ZariskiNullstellensatz

noncomputable section

/-- Definition 1 (Lecture 1). A subset `V ⊆ k^σ` is Zariski closed if it is the zero set
of some collection of polynomials in `k[x_σ]`. -/
def IsZariskiClosed (k : Type*) [Field k] (σ : Type*) (V : Set (σ → k)) : Prop :=
  ∃ S : Set (MvPolynomial σ k), V = {x | ∀ f ∈ S, MvPolynomial.aeval x f = 0}

end
end Lec1ZariskiNullstellensatz
