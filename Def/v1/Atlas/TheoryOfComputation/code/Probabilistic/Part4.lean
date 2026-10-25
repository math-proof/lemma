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
import Structure.v1.Atlas.TheoryOfComputation.code.Probabilistic.Part4


namespace Probabilistic

/-- The semantic equivalence relation on `ROBPPairDesc`: `d.B₁ ≡ d.B₂` as
Boolean functions. -/
def ROBPPairDesc.isEquivalent (d : ROBPPairDesc) : Prop :=
  BPEquiv d.B₁ d.B₂

end Probabilistic
