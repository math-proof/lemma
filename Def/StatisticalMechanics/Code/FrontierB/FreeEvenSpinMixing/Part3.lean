module
public import Theorem.StatisticalMechanics.Code.FrontierB.FreeParityErrorVanishing.Part2
public import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
public import Theorem.StatisticalMechanics.Code.FrontierB.FreeEvenSpinMixing.Part2
open Filter MeasureTheory Set Topology Function
open scoped BigOperators symmDiff


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenSpinMixing.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierB

open ConfigSpace FK Ising Lattice Percolation Sharpness

variable {d : Nat}

noncomputable def freeEvenParityFamilyTerm
    (hd : 1 ≤ d) (mu : Measure (ConfigSpace (Sym2 (Site d))))
    (A B : Finset (Site d)) (k : Nat) : Real :=
  freeEvenParityGap hd mu A B k +
    if Disjoint A (inverseAxisTranslateFinset hd k B) then 0 else 2

end StatMech.FrontierB
