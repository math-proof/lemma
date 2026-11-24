module
public import Def.v1.Atlas.AlgebraicCombinatorics.code.YoungDiagrams.Part2
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungDiagrams
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false
open Polynomial


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QBinomial.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace QBinomial

noncomputable def qBinom : ℕ → ℕ → Polynomial ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | k + 1, j + 1 =>
    if j + 1 > k + 1 then 0
    else qBinom k (j + 1) + (X : Polynomial ℤ) ^ (k - j) * qBinom k j

end QBinomial
