module
public import Def.v1.Atlas.AlgebraicCombinatorics.code.SpernerProperty.Part2
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.SpernerProperty
public import Mathlib.Order.Cover
public import Mathlib.Order.Grade
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Ring
public import Instance.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice
set_option autoImplicit false
open SpernerProperty


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLattice.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace YoungLattice

namespace Lmn

@[ext]
lemma ext {m n : ℕ} {p q : Lmn m n} (h : ∀ i, p.val i = q.val i) : p = q :=
  Subtype.ext (funext h)

end Lmn
end YoungLattice
