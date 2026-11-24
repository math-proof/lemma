module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsing
public import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
public import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingFinite.Part10
public import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingFull
open MeasureTheory Real Set Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFull.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation StatMech.Ising


variable {d : ℕ}


noncomputable def sctInfiniteFieldMag (d : ℕ) (beta h : ℝ) : ℝ :=
  ⨆ n : ℕ, sctOriginMag d beta h n


end Sharpness
end StatMech
