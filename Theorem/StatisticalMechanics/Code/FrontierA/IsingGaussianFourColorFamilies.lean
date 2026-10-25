/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorFamilies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorSwitch.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedBridge.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorFamilies
open Finset
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype V] [DecidableEq V]


theorem exists_finiteTree_sourceComponentSwitch_separatedBranchPattern
    (ends : ι -> Sym2 V) (U : Finset ι) {i j k l : V}
    (c : ↑U -> Fin 4)
    (hloop : ∀ e ∈ U, ¬(ends e).IsDiag) (hkl : k ≠ l)
    (hmix : FiniteTreeMixedPattern ends U i j k l c) :
    ∃ y, FiniteTreeSeparatedBranchPattern ends U i j k l y
      (middleSwapOn U
        (finiteTreeSourceComponentTransfer ends U k c) c) := by
  have hs := finiteTree_sourceComponentSwitch_separatedSources
    ends U c hloop hkl hmix
  obtain ⟨y, hiy, hky⟩ :=
    finiteTree_sourceComponentSwitch_hasCommonVertex
      ends U c hloop hkl hmix
  exact ⟨y, hs, hiy, hky⟩


end StatMech.FrontierA
