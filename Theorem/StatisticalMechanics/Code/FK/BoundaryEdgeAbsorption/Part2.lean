/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryEdgeAbsorption.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
import Def.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.FK

open StatMech.Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
  (boundary : V -> Prop) [DecidablePred boundary]

section NestedBoundary

variable {Vin Vout : Type*} [DecidableEq Vin] [DecidableEq Vout]
  (Gin : SimpleGraph Vin) (Gout : SimpleGraph Vout)
  (incl : Vin → Vout)
  (bdryIn : Vin → Prop) (bdryOut : Vout → Prop)


theorem finiteRootBoundaryEvent_isIncreasing {W : Type*}
    (K : SimpleGraph W) (bdry : W → Prop) (root : W) :
    IsIncreasing (finiteRootBoundaryEvent K bdry root) := by
  intro omega eta home
  rintro ⟨y, hy, hreach⟩
  refine ⟨y, hy, hreach.mono ?_⟩
  intro x z hxz
  rw [openSub_adj] at hxz ⊢
  refine ⟨hxz.1, Bool.eq_true_of_true_le ?_⟩
  simpa [hxz.2] using home s(x, z)

end NestedBoundary
end
end StatMech.FK
