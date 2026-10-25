/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingMass.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.EpsToZeroLattice
import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Sharpness

open Ising Lattice Percolation FieldGhostDict


noncomputable def sctCutSites {d n : ℕ} (T : Finset (sctBox d n)) :
    Finset (Site d) :=
  T.image Subtype.val

end Sharpness
end StatMech
