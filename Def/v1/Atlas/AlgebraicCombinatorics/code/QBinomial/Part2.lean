/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QBinomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicCombinatorics.code.YoungDiagrams.Part2
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungDiagrams
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Fin
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.QBinomial
set_option autoImplicit false

open Polynomial


namespace QBinomial

noncomputable def rankGenPoly (m n : ℕ) : Polynomial ℤ :=
  ∑ p : Lmn m n, (X : Polynomial ℤ) ^ sumParts p

end QBinomial
