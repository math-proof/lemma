/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGraph.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenRiemann.Part6
import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.IsingSusceptibilityPlus.Part2
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeRelabel
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalSimonMass
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusEmbedding
open Finset Set
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.Lattice

open StatMech.Percolation

variable {d k R : Nat}

@[simp] theorem mem_isingTorusImageFinset
    {S : Finset (Site d)} {z : IsingDyadicTorus d k} :
    z ∈ isingTorusImageFinset k S ↔
      ∃ x ∈ S, isingSiteToDyadicTorus k x = z := by
  simp [isingTorusImageFinset]

@[simp] theorem isingSiteToDyadicTorus_origin :
    isingSiteToDyadicTorus k (Percolation.origin d) = 0 := by
  funext i
  simp [isingSiteToDyadicTorus, Percolation.origin]
  exact Int.cast_zero

theorem zero_mem_isingTorusImageFinset
    {S : Finset (Site d)} (hzero : Percolation.origin d ∈ S) :
    (0 : IsingDyadicTorus d k) ∈ isingTorusImageFinset k S := by
  rw [mem_isingTorusImageFinset]
  exact ⟨Percolation.origin d, hzero, isingSiteToDyadicTorus_origin⟩


end StatMech.FrontierA
