/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempPlus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempCorrelation.Part2
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempPlus
open scoped BigOperators
open Finset SimpleGraph MeasureTheory


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Walls


noncomputable def ons_plusLowTempPathSign {d : Nat}
    (config : ConfigSpace (Site d)) {u v : Site d}
    (path : (hypercubicLattice d).Walk u v) : Real :=
  if Even (kwd_crossCount (kwd_sideBoundary config) path) then 1 else -1


end StatMech.Onsager
