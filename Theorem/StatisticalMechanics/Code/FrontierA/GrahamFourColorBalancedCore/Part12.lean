/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
import Theorem.StatisticalMechanics.Code.Ising.GHSThreePoint
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Theorem.StatisticalMechanics.Code.Ising.CurrentWeight.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePropsFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc10ghostfourpoint
import Theorem.StatisticalMechanics.Code.Walls.ghc_urselleqgap
import Theorem.StatisticalMechanics.Code.Walls.vbgtriangle.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc7ghosteven
import Def.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part13
open scoped BigOperators symmDiff
open Finset


namespace StatMech

namespace GrahamGHS

open Ising

open Sharpness


namespace FourColor

variable {W ι : Type*} [Fintype W] [DecidableEq W] [Fintype ι] [DecidableEq ι]


theorem mem_rowComponent_iff (ends : ι → Sym2 W) (m : Finset ι) (c : ↑m → Fin 4)
    (r : Fin 2) (u x : W) :
    x ∈ rowComponent ends m c r u ↔
      Sharpness.RandomCurrent.connK ends (rowClass m c r) u x := by
  simp [rowComponent, Sharpness.RandomCurrent.mem_compOf]


theorem rowsDisconnect_iff_component (ends : ι → Sym2 W) (m : Finset ι)
    (c : ↑m → Fin 4) (u v : W) :
    RowsDisconnect ends m c u v ↔
      v ∉ rowComponent ends m c 0 u ∧ v ∉ rowComponent ends m c 1 u := by
  simp only [RowsDisconnect, mem_rowComponent_iff]


theorem rowComponent_noCrossing (ends : ι → Sym2 W) (m : Finset ι)
    (c : ↑m → Fin 4) (r : Fin 2) (u : W) :
    Sharpness.RandomCurrent.NoCrossingK ends (rowClass m c r)
      (Sharpness.RandomCurrent.notConnCompK ends (rowClass m c r) u) := by
  apply Sharpness.RandomCurrent.noCrossingK_of_event ends (rowClass m c r)
      (Sharpness.RandomCurrent.notConnCompK ends (rowClass m c r) u) u
  · rw [Sharpness.RandomCurrent.mem_notConnCompK]
    exact not_not.mpr Relation.ReflTransGen.refl
  · rfl


end FourColor
end GrahamGHS
end StatMech
