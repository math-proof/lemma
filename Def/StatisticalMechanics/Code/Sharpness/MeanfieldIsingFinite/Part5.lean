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
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingFinite.Part4
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Sharpness

open Ising Lattice Percolation FieldGhostDict


noncomputable def sctEdgeBoundaryCorr {d n : ℕ} (beta : ℝ)
    (T : Finset (sctBox d n)) : Sym2 (sctBox d n) → ℝ :=
  Sym2.lift ⟨fun x y =>
    if x ∈ T ∧ y ∉ T then corrOriginInner d beta (sctCutSites T) x.1
    else if y ∈ T ∧ x ∉ T then corrOriginInner d beta (sctCutSites T) y.1
    else 0, by
      intro x y
      by_cases hx : x ∈ T <;> by_cases hy : y ∈ T <;> simp [hx, hy]⟩


noncomputable def sctInternalBoundaryCorr (d : ℕ) (beta : ℝ) (n : ℕ)
    (T : Finset (sctBox d n)) : ℝ :=
  ∑ e ∈ (sctBoxGraph d n).edgeFinset, sctEdgeBoundaryCorr beta T e


end Sharpness
end StatMech
