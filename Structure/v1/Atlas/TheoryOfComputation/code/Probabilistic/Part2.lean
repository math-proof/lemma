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
public import Def.v1.Atlas.TheoryOfComputation.code.Probabilistic


public section

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
