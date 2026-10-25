/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxCurrentPatternFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.CurrentParityDetermination.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.PlusBoxCurrentParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.BoxCurrentPatternFactor
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice

open StatMech.IsingFK

def currentParityPatternCylinder {E : Type*} (F : Finset E)
    (odd : ↑F → Bool) : Set (InfiniteCurrentConfig E) :=
  currentCylinder F {a | currentLocalParity a = odd}

noncomputable def pullbackParityPattern
    (d n : ℕ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n) (odd : ↑F → Bool) :
    ↑(boxPullbackEdgeSubtypes d n F) → Bool :=
  odd ∘ boxPullbackEdgeEquiv d n F hF

end StatMech.FrontierB
