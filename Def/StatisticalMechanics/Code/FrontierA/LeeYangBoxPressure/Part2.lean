/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeSum
import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingState.Part2
import Theorem.StatisticalMechanics.Code.Ising.PressureSurfaceVolume.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangLogDerivativeBound.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangBoxPressure.Part2
open scoped BigOperators
open Finset Filter Topology Set SimpleGraph


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FK StatMech.Lattice StatMech.Sharpness


variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def isingBoxCauchyBound
    (d m : ℕ) (beta h : ℝ) (n : ℕ) : ℝ :=
  let r := ((ecz_T m n) ^ d : ℝ) * (Fintype.card (boxVerts d m) : ℝ) /
    (Fintype.card (boxVerts d n) : ℝ)
  (Real.log 2 + |beta| * |h|) * (1 - r) +
    |beta| * ((((boxGraph d n).edgeFinset.card : ℝ) -
      ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)) /
        (Fintype.card (boxVerts d n) : ℝ)) +
    |1 - r| * |isingBoxPressureSeq d beta h m|

end StatMech.FrontierA
