module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismFaces.Part2
public import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
public import Inductive.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionTouchingBondGeometry


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.Ising StatMech.IsingFK
  StatMech.Percolation


abbrev OddPrismTouchIndexSum (n : Nat) :=
  (Fin (2 * n) × Fin (2 * n + 1) × Fin (2 * n + 1)) ⊕
  ((Fin (2 * n + 1) × Fin (2 * n) × Fin (2 * n + 1)) ⊕
  ((Fin (2 * n + 1) × Fin (2 * n + 1) × Fin (2 * n)) ⊕
  ((Fin (2 * n + 1) × Fin (2 * n + 1)) ⊕
  ((Fin (2 * n + 1) × Fin (2 * n + 1)) ⊕
  ((Fin (2 * n + 1) × Fin (2 * n + 1)) ⊕
  ((Fin (2 * n + 1) × Fin (2 * n + 1)) ⊕
  ((Fin (2 * n + 1) × Fin (2 * n + 1)) ⊕
    (Fin (2 * n + 1) × Fin (2 * n + 1)))))))))


end StatMech.FrontierA
