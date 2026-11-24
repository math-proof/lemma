module
public import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingMass.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.EpsToZeroLattice
public import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
public import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
public import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingFinite.Part9
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


noncomputable def sctExternalBoxPairs (d n : ℕ) :
    Finset (sctBox d n × Site d) :=
  (Finset.univ : Finset (sctBox d n)).biUnion fun x =>
    (sctExteriorNeighbours d n x.1).image fun y => (x, y)

end Sharpness
end StatMech
