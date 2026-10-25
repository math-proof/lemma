/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Algebra.Polynomial.Roots
import Def.v1.Atlas.TheoryOfComputation.code.BPP.Part3
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.Order.Archimedean.Basic
import Structure.v1.Atlas.TheoryOfComputation.code.Probabilistic


namespace Probabilistic

/-- A graph-pair description `d` is *isomorphic* if there exists a graph
isomorphism `d.G ≃g d.H`. This is the property defining membership in `ISO`. -/
def GraphPairDesc.isIsomorphic (d : GraphPairDesc) : Prop :=
  Nonempty (d.G ≃g d.H)

end Probabilistic
