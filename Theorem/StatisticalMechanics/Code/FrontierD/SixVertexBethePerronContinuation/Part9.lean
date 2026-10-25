/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle.Part3
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part9
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem card_sixVertexDefectSet
    {N n : Nat} (hN : 0 < N) (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) :
    (sixVertexDefectSet hN x).card = N - 2 * n := by
  rw [sixVertexDefectSet,
    Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  rw [Finset.card_union_of_disjoint
    (sixVertexSector_disjoint_cyclicSucc_of_noAdjacent hN x hx),
    Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hxcard : (x : Finset (Fin N)).card = n := x.prop
  omega

theorem card_sixVertexFixedChargeDefectSet
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k))
    (hx : SixVertexSectorNoAdjacent x) :
    (sixVertexDefectSet (sixVertexFourWidth_pos r k) x).card = 2 * r := by
  rw [card_sixVertexDefectSet (sixVertexFourWidth_pos r k) x hx,
    sixVertexFourWidth, sixVertexFixedChargeBetheParticleCount_eq]
  omega


end
end StatMech.FrontierD
