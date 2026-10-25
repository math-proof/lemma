/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumFactor.Part3
open MeasureTheory Set


namespace StatMech.FK

open Lattice Percolation


def pottsBlockLabels {κ ι q : Type*} (F : κ -> Finset ι)
    (label : ι -> q) : ∀ k, F k -> q :=
  fun _ x => label x


def pottsBlockSums {κ ι : Type*} {q : Nat} [NeZero q]
    (F : κ -> Finset ι) (label : ι -> Fin q) : κ -> Fin q :=
  fun k => ∑ x : F k, label x


end StatMech.FK
