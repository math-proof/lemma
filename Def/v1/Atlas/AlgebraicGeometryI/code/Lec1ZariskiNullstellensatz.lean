/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec1ZariskiNullstellensatz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.Order.KrullDimension
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

@[expose] public section

open MvPolynomial AlgebraicGeometry CategoryTheory


namespace Lec1ZariskiNullstellensatz

noncomputable section

/-- Definition 1 (Lecture 1). A subset `V ⊆ k^σ` is Zariski closed if it is the zero set
of some collection of polynomials in `k[x_σ]`. -/
def IsZariskiClosed (k : Type*) [Field k] (σ : Type*) (V : Set (σ → k)) : Prop :=
  ∃ S : Set (MvPolynomial σ k), V = {x | ∀ f ∈ S, MvPolynomial.aeval x f = 0}

end
end Lec1ZariskiNullstellensatz
