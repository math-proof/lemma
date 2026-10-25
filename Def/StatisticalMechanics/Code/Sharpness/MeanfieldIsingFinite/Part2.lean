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
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingFinite
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Sharpness

open Ising Lattice Percolation FieldGhostDict


noncomputable def sctCutVertexEquiv {d n : ℕ} (T : Finset (sctBox d n)) :
    {x : sctBox d n // x ∈ T} ≃ {z : Site d // z ∈ sctCutSites T} :=
  Equiv.ofBijective
    (fun x => (⟨x.1.1, mem_sctCutSites.mpr x.2⟩ :
      {z : Site d // z ∈ sctCutSites T}))
    ⟨by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : {z : Site d // z ∈ sctCutSites T} => z.1) h,
    by
      intro z
      have hz : z.1 ∈ T.image Subtype.val := z.2
      rw [Finset.mem_image] at hz
      obtain ⟨x, hx, hv⟩ := hz
      refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
      exact hv⟩


end Sharpness
end StatMech
