module
public import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingMass.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.EpsToZeroLattice
public import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
public import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
open Finset SimpleGraph
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Sharpness

open Ising Lattice Percolation FieldGhostDict


noncomputable def sctCutSites {d n : ℕ} (T : Finset (sctBox d n)) :
    Finset (Site d) :=
  T.image Subtype.val

end Sharpness
end StatMech
