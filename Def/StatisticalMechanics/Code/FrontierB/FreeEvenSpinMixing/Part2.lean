/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenSpinMixing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FreeParityErrorVanishing.Part2
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.FrontierB.FreeEvenSpinMixing
open Filter MeasureTheory Set Topology Function
open scoped BigOperators symmDiff


namespace StatMech.FrontierB

open ConfigSpace FK Ising Lattice Percolation Sharpness

variable {d : Nat}

noncomputable def freeEvenParityGap
    (hd : 1 ≤ d) (mu : Measure (ConfigSpace (Sym2 (Site d))))
    (A B : Finset (Site d)) (k : Nat) : Real :=
  mu.real (allClustersEvenEvent (hypercubicLattice d)
      (A ∪ inverseAxisTranslateFinset hd k B)) -
    mu.real (allClustersEvenEvent (hypercubicLattice d) A) *
      mu.real (allClustersEvenEvent (hypercubicLattice d) B)

end StatMech.FrontierB
