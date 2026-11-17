/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Blowups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.AdjoinRoot

@[expose] public section

/-- Algebra isomorphism resolving a nodal singularity: the quotient
`k[X][Y] / ⟨Y - C(X² - 1)⟩` is isomorphic (over `k[X]`) to `k[X]`. -/
noncomputable def nodeResolveIso (k : Type*) [CommRing k] :
    (Polynomial (Polynomial k) ⧸ Ideal.span
      {Polynomial.X - Polynomial.C ((Polynomial.X : Polynomial k) ^ 2 - 1)})
    ≃ₐ[Polynomial k] Polynomial k :=
  Polynomial.quotientSpanXSubCAlgEquiv (Polynomial.X ^ 2 - 1)

