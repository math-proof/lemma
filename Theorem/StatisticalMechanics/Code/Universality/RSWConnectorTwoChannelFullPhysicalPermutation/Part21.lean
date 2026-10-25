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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part21
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysicalTargetCarrierGeometry_iff_local
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) (f g : Site 2) :
    RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g ↔
      RlcTwoChannelFullPhysicalTargetCarrierLocal gamma gamma' f g := by
  constructor
  · rintro ⟨target, htarget⟩
    induction hedge : target.1 using Sym2.inductionOn with
    | _ x y =>
        rw [hedge, Sym2.map_mk, Sym2.eq_iff] at htarget
        have hxy : (rlc_connectorTwoChannelGraph gamma gamma').Adj x y :=
          (SimpleGraph.mem_edgeSet _).mp (hedge ▸ target.2)
        rcases htarget with ⟨hxf, hyg⟩ | ⟨hxg, hyf⟩
        · have hf : rlc_dualReflect f ∈
              rect (-2 * n) (2 * n) (-n) n := hxf ▸ x.2
          have hg : rlc_dualReflect g ∈
              rect (-2 * n) (2 * n) (-n) n := hyg ▸ y.2
          refine ⟨hf, hg, ?_⟩
          have hx : x = ⟨rlc_dualReflect f, hf⟩ := Subtype.ext hxf
          have hy : y = ⟨rlc_dualReflect g, hg⟩ := Subtype.ext hyg
          simpa [hx, hy] using hxy
        · have hg : rlc_dualReflect g ∈
              rect (-2 * n) (2 * n) (-n) n := hxg ▸ x.2
          have hf : rlc_dualReflect f ∈
              rect (-2 * n) (2 * n) (-n) n := hyf ▸ y.2
          refine ⟨hf, hg, ?_⟩
          have hx : x = ⟨rlc_dualReflect g, hg⟩ := Subtype.ext hxg
          have hy : y = ⟨rlc_dualReflect f, hf⟩ := Subtype.ext hyf
          simpa [hx, hy] using hxy.symm
  · rintro ⟨hf, hg, hfg⟩
    let target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
      ⟨s(⟨rlc_dualReflect f, hf⟩, ⟨rlc_dualReflect g, hg⟩),
        (SimpleGraph.mem_edgeSet _).mpr hfg⟩
    exact ⟨target, by simp [target, Sym2.map_mk]⟩


end
end StatMech.Universality
