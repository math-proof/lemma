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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusEmbedding.Part2
open Finset Set
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.Lattice

open StatMech.Percolation

variable {d k R : Nat}

noncomputable def isingTorusImageEquiv
    (S : Finset (Site d))
    (hinj : Set.InjOn (isingSiteToDyadicTorus k) (↑S : Set (Site d))) :
    {x // x ∈ S} ≃ {z // z ∈ isingTorusImageFinset k S} where
  toFun x := ⟨isingSiteToDyadicTorus k x.1, by
    rw [mem_isingTorusImageFinset]
    exact ⟨x.1, x.2, rfl⟩⟩
  invFun z := ⟨(mem_isingTorusImageFinset.mp z.2).choose,
    (mem_isingTorusImageFinset.mp z.2).choose_spec.1⟩
  left_inv x := by
    apply Subtype.ext
    let hspec := (mem_isingTorusImageFinset.mp
      ((⟨isingSiteToDyadicTorus k x.1, by
        rw [mem_isingTorusImageFinset]
        exact ⟨x.1, x.2, rfl⟩⟩ :
        {z // z ∈ isingTorusImageFinset k S}).2)).choose_spec
    exact hinj hspec.1 x.2 hspec.2
  right_inv z := by
    apply Subtype.ext
    exact (mem_isingTorusImageFinset.mp z.2).choose_spec.2

end StatMech.FrontierA
