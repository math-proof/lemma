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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusEmbedding
open Finset Set
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.Lattice

open StatMech.Percolation

variable {d k R : Nat}

noncomputable def isingTorusImageFinset
    (k : Nat) (S : Finset (Site d)) : Finset (IsingDyadicTorus d k) :=
  S.image (isingSiteToDyadicTorus k)

end StatMech.FrontierA
