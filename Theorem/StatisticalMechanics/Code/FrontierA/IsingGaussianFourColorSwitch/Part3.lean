/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCorrections.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorSwitch.Part2
open Finset
open scoped symmDiff
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype V] [DecidableEq V]


theorem exists_finiteTreeMiddleTransferWitness_of_mixed
    (ends : ι -> Sym2 V) (U : Finset ι) {i j k l : V}
    (c : ↑U -> Fin 4)
    (hloop : ∀ e ∈ U, ¬(ends e).IsDiag) (hkl : k ≠ l)
    (hmix : FiniteTreeMixedPattern ends U i j k l c) :
    ∃ X, FiniteTreeMiddleTransferWitness ends U k l c X := by
  have hconn : connK ends (colorClass U c 1) k l :=
    StatMech.Walls.gc6_pairingPath_abstract ends
      (colorClass U c 1) (colorClass U c 1)
      (fun e he => hloop e (colorClass_subset U c 1 he))
      Finset.Subset.rfl hmix.2.1 hkl
  obtain ⟨X, hX, hsrc⟩ := exists_conn_set ends
    (colorClass U c 1) hconn hkl
  refine ⟨X, ?_, hsrc, ?_⟩
  · exact hX.trans Finset.subset_union_left
  · exact path_exists ends X
      (fun e he => hloop e
        (colorClass_subset U c 1 (hX he))) k l
      (by rw [← mem_sources, hsrc]; simp)
      (by
        intro x hx
        rw [← mem_sources, hsrc] at hx
        simpa using hx)
      hkl


end StatMech.FrontierA
