/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellRN.Part5
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part5
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossing.Part4
open SimpleGraph Set
open scoped BigOperators


namespace StatMech.BeffaraDC

open StatMech.Onsager


def torusSquareVertexSet (L n : ℕ) : Set (ZMod L × ZMod L) :=
  {x | x.1.val ≤ n ∧ x.2.val ≤ n}


def torusSquareHorizontalCrossing (L : ℕ) [Fact (2 < L)] (n : ℕ)
    (omega : TorusAmbientConfig L) : Prop :=
  ∃ (x y : ZMod L × ZMod L)
      (hx : x ∈ torusSquareVertexSet L n)
      (hy : y ∈ torusSquareVertexSet L n),
    x.1.val = 0 ∧ y.1.val = n ∧
      ((FK.openSub (onsTorusGraph L) (torusAmbientConfigExtend L omega)).induce
        (torusSquareVertexSet L n)).Reachable ⟨x, hx⟩ ⟨y, hy⟩


noncomputable def torusSquareHorizontalCrossingEvent
    (L : ℕ) [Fact (2 < L)] (n : ℕ) : Finset (TorusAmbientConfig L) := by
  classical
  exact Finset.univ.filter (torusSquareHorizontalCrossing L n)

end StatMech.BeffaraDC
