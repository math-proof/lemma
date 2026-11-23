/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Algebra.Polynomial.Roots
public import Def.v1.Atlas.TheoryOfComputation.code.BPP.Part3
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Structure.v1.Atlas.TheoryOfComputation.code.Probabilistic.Part4

@[expose] public section

namespace Probabilistic

/-- The semantic equivalence relation on `ROBPPairDesc`: `d.B₁ ≡ d.B₂` as
Boolean functions. -/
def ROBPPairDesc.isEquivalent (d : ROBPPairDesc) : Prop :=
  BPEquiv d.B₁ d.B₂

end Probabilistic
