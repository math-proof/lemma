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
public import Def.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice
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

instance instPartialOrder (m n : ℕ) : PartialOrder (Lmn m n) :=
  Subtype.partialOrder _

noncomputable instance instDecidableEq (m n : ℕ) : DecidableEq (Lmn m n) :=
  Classical.decEq _

noncomputable instance instFintype (m n : ℕ) : Fintype (Lmn m n) := by
  classical
  exact Fintype.subtype (Finset.univ.filter (fun f : Fin m → Fin (n + 1) => Antitone f))
    (fun f => by simp [Finset.mem_filter])

end Lmn
end YoungLattice
