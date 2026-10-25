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
import Def.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part18
open scoped BigOperators symmDiff
open Finset


namespace StatMech

namespace GrahamGHS

open Ising

open Sharpness


namespace FourColor

variable {W ι : Type*} [Fintype W] [DecidableEq W] [Fintype ι] [DecidableEq ι]


theorem leftRowData_card_eq_weightedSum (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) :
    Fintype.card (leftRowData ends m j k l zero) =
      ∑ K ∈ leftRowSupports ends m j k l zero, rowSupportWeight ends m K := by
  classical
  calc
    Fintype.card (leftRowData ends m j k l zero) =
        ∑ K : leftRowSupportIndex ends m j k l zero, rowSupportWeight ends m K.1 := by
      change Fintype.card (Σ K : leftRowSupportIndex ends m j k l zero,
        boundarySector ends K.1 {j, k} × boundarySector ends (m \ K.1) {k, l}) = _
      calc
        Fintype.card (Σ K : leftRowSupportIndex ends m j k l zero,
            boundarySector ends K.1 {j, k} × boundarySector ends (m \ K.1) {k, l}) =
            ∑ K : leftRowSupportIndex ends m j k l zero,
              Fintype.card (boundarySector ends K.1 {j, k} ×
                boundarySector ends (m \ K.1) {k, l}) := Fintype.card_sigma
        _ = _ := by
          apply Finset.sum_congr rfl
          intro K _
          rw [Fintype.card_prod]
          have hKA : boundarySector ends K.1 {j, k} :=
            ⟨K.1, Finset.Subset.rfl, K.2.2.1⟩
          have hLB : boundarySector ends (m \ K.1) {k, l} :=
            ⟨m \ K.1, Finset.Subset.rfl, K.2.2.2.1⟩
          rw [boundarySector_card_eq_cycle ends K.1 {j, k} hKA,
            boundarySector_card_eq_cycle ends (m \ K.1) {k, l} hLB]
          rfl
    _ = ∑ K ∈ leftRowSupports ends m j k l zero, rowSupportWeight ends m K := by
      symm
      exact Finset.sum_subtype _ (fun K => by simp [leftRowSupports, leftRowSupportIndex]) _

theorem leftFiber_card_eq_weightedSum (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) :
    Fintype.card (leftFiber ends m {j, k} {k, l} k zero) =
      ∑ K ∈ leftRowSupports ends m j k l zero, rowSupportWeight ends m K := by
  rw [Fintype.card_congr (leftFiberEquivRowData ends m j k l zero),
    leftRowData_card_eq_weightedSum]

end FourColor
end GrahamGHS
end StatMech
