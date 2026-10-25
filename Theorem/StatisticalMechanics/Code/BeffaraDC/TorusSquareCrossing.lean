/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellRN.Part5
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part5
import Def.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossing
open SimpleGraph Set
open scoped BigOperators


namespace StatMech.BeffaraDC

open StatMech.Onsager


@[simp] theorem torusCoordSwap_apply (L : ℕ) (x : ZMod L × ZMod L) :
    torusCoordSwap L x = (x.2, x.1) := rfl

@[simp] theorem torusCoordSwap_symm (L : ℕ) :
    (torusCoordSwap L).symm = torusCoordSwap L := rfl


theorem onsTorusGraph_adj_coordSwap (L : ℕ) [Fact (2 < L)]
    (x y : ZMod L × ZMod L) :
    (onsTorusGraph L).Adj (torusCoordSwap L x) (torusCoordSwap L y) ↔
      (onsTorusGraph L).Adj x y := by
  change onsTorusAdj L (x.2, x.1) (y.2, y.1) ↔ onsTorusAdj L x y
  unfold onsTorusAdj
  tauto


theorem torusCoordSwap_mem_edgeFinset_iff (L : ℕ) [Fact (2 < L)]
    (e : Sym2 (ZMod L × ZMod L)) :
    Sym2.map (torusCoordSwap L) e ∈ (onsTorusGraph L).edgeFinset ↔
      e ∈ (onsTorusGraph L).edgeFinset := by
  induction e using Sym2.ind with
  | _ x y =>
      simp only [Sym2.map_mk, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet]
      exact onsTorusGraph_adj_coordSwap L x y


end StatMech.BeffaraDC
