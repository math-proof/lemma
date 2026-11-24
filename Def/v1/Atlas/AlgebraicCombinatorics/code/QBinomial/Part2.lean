module
public import Def.v1.Atlas.AlgebraicCombinatorics.code.YoungDiagrams.Part2
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungDiagrams
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Algebra.BigOperators.Fin
public import Theorem.v1.Atlas.AlgebraicCombinatorics.code.QBinomial
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

noncomputable def rankGenPoly (m n : ℕ) : Polynomial ℤ :=
  ∑ p : Lmn m n, (X : Polynomial ℤ) ^ sumParts p

end QBinomial
