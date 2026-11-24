module
public import Def.v1.Atlas.AlgebraicCombinatorics.code.OrderRaising
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.OrderRaising
public import Mathlib.Data.Finset.Card
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/BooleanSperner.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace SpernerProperty

section BooleanSperner

variable (n : ℕ)

def booleanComplement (s : BooleanPoset n) : BooleanPoset n :=
  Finset.univ \ s

end BooleanSperner
end SpernerProperty
