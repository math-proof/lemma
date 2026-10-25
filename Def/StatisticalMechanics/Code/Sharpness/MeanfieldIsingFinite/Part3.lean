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
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingFinite.Part2
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Sharpness

open Ising Lattice Percolation FieldGhostDict


noncomputable def sctCurrentCutMass (d : ℕ) (beta h : ℝ) (n : ℕ)
    (T : Finset (sctBox d n)) : ℝ :=
  isingCutMass (withGhost (sctBoxGraph d n)) beta
    (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)


noncomputable def sctOrientedCutMass (d : ℕ) (beta h : ℝ) (n : ℕ)
    (x y : sctBox d n) : ℝ :=
  ∑ T : Finset (sctBox d n),
    if sctBoxOrigin d n ∈ T ∧ x ∈ T ∧ y ∉ T then
      corrOriginInner d beta (sctCutSites T) x.1 *
        sctCurrentCutMass d beta h n T
    else 0


end Sharpness
end StatMech
