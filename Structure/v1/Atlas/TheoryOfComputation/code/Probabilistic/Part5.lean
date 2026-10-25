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
import Def.v1.Atlas.TheoryOfComputation.code.Probabilistic.Part4


namespace Probabilistic

/-- A faithful encoding of `ROBPPairDesc` as strings over alphabet `Γ`, used
to turn the abstract equivalence problem into a language `EQ_ROBP ⊆ List Γ`. -/
structure ROBPPairEncoding (Γ : Type) where
  encode : ROBPPairDesc → List Γ
  decode : List Γ → Option ROBPPairDesc
  encode_injective : Function.Injective encode
  decode_encode : ∀ d, decode (encode d) = some d

end Probabilistic
