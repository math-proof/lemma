/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_cardorbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part8
import Def.StatisticalMechanics.Code.Walls.rmr_cardorbit.Part2
open Finset


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem cardOrbit_box (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    #(boxOrbit A B k) = #(slabBox A B k) := by
  rw [← Fintype.card_coe (boxOrbit A B k), ← Fintype.card_coe (slabBox A B k)]
  exact Fintype.card_congr (boxOrbitEquivSlabBox A B k)


theorem cardOrbit_img (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    #(imgOrbit A B k) = #(slabImg A B k) := by
  rw [← Fintype.card_coe (imgOrbit A B k), ← Fintype.card_coe (slabImg A B k)]
  exact Fintype.card_congr (imgOrbitEquivSlabImg A B k)


theorem cardOrbit (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    #(boxOrbit A B k) = #(slabBox A B k) ∧ #(imgOrbit A B k) = #(slabImg A B k) :=
  ⟨cardOrbit_box A B k, cardOrbit_img A B k⟩

end StatMech.Walls
