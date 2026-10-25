/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
open MeasureTheory Set


namespace StatMech.FK

open Lattice Percolation


def pottsLabelShift {d q : Nat} (g : Multiplicative (Site d))
    (label : Site d -> Fin q) : Site d -> Fin q :=
  fun x => label (g⁻¹ • x)


noncomputable def pottsClusterSumSpin {d q : Nat} [NeZero q]
    (boundaryColor : Fin q) (omega : ConfigSpace (Sym2 (Site d)))
    (label : Site d -> Fin q) (x : Site d) : Fin q := by
  classical
  exact if hfinite : (cluster d omega x).Finite then
      ∑ y ∈ hfinite.toFinset, label y
    else boundaryColor


end StatMech.FK
