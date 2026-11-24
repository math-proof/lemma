module
public import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingMass.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.EpsToZeroLattice
public import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
public import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
public import Def.StatisticalMechanics.Code.Sharpness.MeanfieldIsingFinite
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


@[simp]
theorem mem_sctCutSites {d n : ℕ} {T : Finset (sctBox d n)} {x : sctBox d n} :
    x.1 ∈ sctCutSites T ↔ x ∈ T := by
  classical
  constructor
  · intro hx
    rw [sctCutSites, Finset.mem_image] at hx
    obtain ⟨y, hy, hv⟩ := hx
    have : y = x := Subtype.ext hv
    rwa [← this]
  · intro hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩


end Sharpness
end StatMech
