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
public import Structure.v1.Atlas.TheoryOfComputation.code.Probabilistic

@[expose] public section

namespace Probabilistic

/-- A graph-pair description `d` is *isomorphic* if there exists a graph
isomorphism `d.G ≃g d.H`. This is the property defining membership in `ISO`. -/
def GraphPairDesc.isIsomorphic (d : GraphPairDesc) : Prop :=
  Nonempty (d.G ≃g d.H)

end Probabilistic
