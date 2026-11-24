module
public import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingMass.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.EpsToZeroLattice
public import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
public import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
public import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingFinite.Part5
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


noncomputable def sctBoxize (d n : ℕ) (z : Site d) : sctBox d n :=
  if hz : z ∈ box d n then ⟨z, hz⟩ else sctBoxOrigin d n

end Sharpness
end StatMech
