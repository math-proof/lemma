/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicCombinatorics.code.SpernerProperty.Part2
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.SpernerProperty
import Mathlib.Order.Cover
import Mathlib.Order.Grade
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice
set_option autoImplicit false

open SpernerProperty


namespace YoungLattice

namespace Lmn

def sumParts {m n : ℕ} (p : Lmn m n) : ℕ :=
  ∑ i : Fin m, (p.val i).val

def zero (m n : ℕ) : Lmn m n :=
  ⟨fun _ => 0, fun _ _ _ => le_refl _⟩

def top (m n : ℕ) : Lmn m n :=
  ⟨fun _ => Fin.last n, fun _ _ _ => le_refl _⟩

end Lmn
end YoungLattice
