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
import Def.v1.Atlas.AlgebraicCombinatorics.code.WreathOrbits.Part2
set_option autoImplicit false


namespace WreathOrbits

variable {m n : ℕ}

lemma rowSize_actOnSet (g : WreathElem m n) (S : Finset (Fin m × Fin n)) (i : Fin m) :
    rowSize (g.actOnSet S) (g.σ i) = rowSize S i := by
  simp only [rowSize, WreathElem.actOnSet]
  have : (S.image g.actOn).filter (fun p => p.1 = g.σ i) =
         (S.filter (fun p => p.1 = i)).image g.actOn := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_image, WreathElem.actOn, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨x, y⟩, hxy, rfl, rfl⟩, h⟩
      refine ⟨⟨x, y⟩, ⟨hxy, g.σ.injective h⟩, rfl, rfl⟩
    · rintro ⟨⟨x, y⟩, ⟨hxy, hxi⟩, rfl, rfl⟩
      exact ⟨⟨⟨x, y⟩, hxy, rfl, rfl⟩, by rw [hxi]⟩
  rw [this, Finset.card_image_of_injective _ g.actOn_injective]

end WreathOrbits
