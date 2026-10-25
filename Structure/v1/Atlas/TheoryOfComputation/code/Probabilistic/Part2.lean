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
import Def.v1.Atlas.TheoryOfComputation.code.Probabilistic


namespace Probabilistic

/-- A faithful encoding of graph-pair descriptions as strings over alphabet `Γ`,
specified by an injective `encode` function and a `decode` function that inverts
it. Used to turn the mathematical object `GraphPairDesc` into the language
`ISO ⊆ List Γ`. -/
structure GraphPairEncoding (Γ : Type) where
  encode : GraphPairDesc → List Γ
  decode : List Γ → Option GraphPairDesc
  encode_injective : Function.Injective encode
  decode_encode : ∀ d, decode (encode d) = some d

end Probabilistic
