/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice.Part3
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungLattice
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.List.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.GetD
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Basic
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.WreathOrbits.Part2
set_option autoImplicit false


namespace WreathOrbits

variable {m n : ℕ}

def IsLeftJustified (S : Finset (Fin m × Fin n)) : Prop :=
  ∀ (i : Fin m) (j j' : Fin n), (i, j) ∈ S → j' < j → (i, j') ∈ S

def IsGridYoung (S : Finset (Fin m × Fin n)) : Prop :=
  IsLeftJustified S ∧ Antitone (rowSize S)

end WreathOrbits
