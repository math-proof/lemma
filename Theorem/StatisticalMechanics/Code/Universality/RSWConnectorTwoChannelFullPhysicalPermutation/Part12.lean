/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part13
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_not_crossesCut_iff_monochromatic
    {V : Type*} (A : Set V) (e : Sym2 V) :
    ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A e ↔
      PairedEdgeMonochromatic A e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [rlc_twoChannelFullPhysicalEdgeCrossesCut,
        PairedEdgeMonochromatic, Sym2.eq_iff]
      constructor
      · intro h a b hab
        have huv : u ∈ A ↔ v ∈ A := by
          have hsep : ¬((u ∈ A ∧ v ∉ A) ∨ (v ∈ A ∧ u ∉ A)) := by
            intro hcross
            exact h ⟨u, v, Or.inl ⟨rfl, rfl⟩, hcross⟩
          tauto
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact huv
        · exact huv.symm
      · intro h hcross
        obtain ⟨a, b, hab, hsep⟩ := hcross
        have hm := h a b hab
        rcases hsep with ⟨ha, hb⟩ | ⟨hb, ha⟩
        · exact hb (hm.mp ha)
        · exact ha (hm.mpr hb)


end
end StatMech.Universality
