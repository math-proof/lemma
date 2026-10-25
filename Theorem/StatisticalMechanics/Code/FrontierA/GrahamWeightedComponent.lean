/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedComponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.gh4eq22.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsing.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.Claim1IsingFull.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Def.StatisticalMechanics.Code.FrontierA.GrahamWeightedComponent
open Finset SimpleGraph
open scoped symmDiff


namespace StatMech.FrontierA

open StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Walls

variable {ι W : Type*} [DecidableEq ι] [Fintype ι]
  [DecidableEq W] [Fintype W]


theorem grahamComponentComplement_not_mem
    (ends : ι → Sym2 W) (m : Finset ι) (u : W) :
    u ∉ grahamComponentComplement ends m u := by
  rw [grahamComponentComplement, mem_notConnCompK]
  exact not_not_intro Relation.ReflTransGen.refl


theorem grahamComponentComplement_noCrossing
    (ends : ι → Sym2 W) (m : Finset ι) (u : W) :
    NoCrossingK ends m (grahamComponentComplement ends m u) := by
  apply noCrossingK_of_event ends m _ u
  · exact grahamComponentComplement_not_mem ends m u
  · rfl


theorem grahamComponentComplement_noCrossing_of_subset
    (ends : ι → Sym2 W) (m K : Finset ι) (u : W) (hKm : K ⊆ m) :
    NoCrossingK ends K (grahamComponentComplement ends m u) := by
  intro i hi
  exact grahamComponentComplement_noCrossing ends m u i (hKm hi)


end StatMech.FrontierA
