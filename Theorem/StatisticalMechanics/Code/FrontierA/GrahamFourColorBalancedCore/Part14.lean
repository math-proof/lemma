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
import Def.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
open scoped BigOperators symmDiff
open Finset


namespace StatMech

namespace GrahamGHS

open Ising

open Sharpness


namespace FourColor

variable {W ι : Type*} [Fintype W] [DecidableEq W] [Fintype ι] [DecidableEq ι]


theorem rowDataToLeftFiber_leftInverse (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) (c : leftFiber ends m {j, k} {k, l} k zero) :
    rowDataToLeftFiber ends m j k l zero (leftFiberToRowData ends m j k l zero c) = c := by
  apply Subtype.ext
  funext i
  have hci : c.1 i = 0 ∨ c.1 i = 1 ∨ c.1 i = 2 ∨ c.1 i = 3 := by omega
  rcases hci with hci | hci | hci | hci <;>
    simp [rowDataToLeftFiber, leftFiberToRowData, coloringOfRowData, rowClass, colorClass, hci]

theorem rowDataToLeftFiber_injective (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) : Function.Injective (rowDataToLeftFiber ends m j k l zero) := by
  rintro ⟨dK, dP, dQ⟩ ⟨eK, eP, eQ⟩ hde
  have hc := congrArg Subtype.val hde
  change coloringOfRowData m dK.1 dP.1 dQ.1 =
    coloringOfRowData m eK.1 eP.1 eQ.1 at hc
  have hdcl := colorClasses_coloringOfRowData dK.2.1 dP.2.1 dQ.2.1
  have hecl := colorClasses_coloringOfRowData eK.2.1 eP.2.1 eQ.2.1
  have hdr := rowClasses_coloringOfRowData dK.2.1 dP.2.1 dQ.2.1
  have her := rowClasses_coloringOfRowData eK.2.1 eP.2.1 eQ.2.1
  have hK : dK.1 = eK.1 := by
    rw [← hdr.1, ← her.1, hc]
  have hK' : dK = eK := Subtype.ext hK
  subst eK
  have hP : dP.1 = eP.1 := by
    rw [← hdcl.1, ← hecl.1, hc]
  have hQ : dQ.1 = eQ.1 := by
    rw [← hdcl.2.2.1, ← hecl.2.2.1, hc]
  congr
  · exact Subtype.ext hP
  · exact Subtype.ext hQ

end FourColor
end GrahamGHS
end StatMech
