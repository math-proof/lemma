module
public import Theorem.StatisticalMechanics.Code.FrontierA.FiniteFamilyDiagonalSelection
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalTorusLocalObservables.Part4
open Filter Finset Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusGrowingSupport.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech Ising Lattice Sharpness StatMech.FrontierB

noncomputable section

variable {d : Nat}

def growingRowOrderFamily (n : Nat) : Finset (Nat × Nat) :=
  {n} ×ˢ Finset.range (n + 1)


end
end StatMech.FrontierA
