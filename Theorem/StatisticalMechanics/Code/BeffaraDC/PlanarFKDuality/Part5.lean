/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Def.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part5
open Finset SimpleGraph Set


namespace StatMech

namespace BeffaraDC

open Lattice Ising Walls


theorem pfd_subgraph_edgeCount_le (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (hKP : K ≤ P.G) : K.edgeSet.ncard ≤ P.G.edgeFinset.card := by
  have hset : K.edgeSet ⊆ P.G.edgeSet := SimpleGraph.edgeSet_mono hKP
  have hn := Set.ncard_le_ncard hset (Set.toFinite P.G.edgeSet)
  simpa only [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card'] using hn


theorem pfd_weight_duality (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (hKP : K ≤ P.G) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    pfdPrimalWeight P p q K * q ^ (P.G.edgeFinset.card + 1) =
      (p / (1 - dualParam p q)) ^ P.G.edgeFinset.card * q ^ Nat.card P.V *
        pfdDualWeight P (dualParam p q) q K := by
  let m := P.G.edgeFinset.card
  let o := K.edgeSet.ncard
  let k := Nat.card K.ConnectedComponent
  let kd := Nat.card (pfdClosedDual P K).ConnectedComponent
  let v := Nat.card P.V
  have hom : o ≤ m := pfd_subgraph_edgeCount_le P K hKP
  have hedge := dlt_edgeProduct_duality hp hp1 hq m o hom
  have heuler : v + kd = o + k + 1 := pfd_clusterEuler P K hKP
  have hpow : q ^ o * q ^ k * q = q ^ v * q ^ kd := by
    calc
      q ^ o * q ^ k * q = q ^ (o + k + 1) := by
        rw [← pow_add, ← pow_succ]
      _ = q ^ (v + kd) := congrArg (q ^ ·) heuler.symm
      _ = q ^ v * q ^ kd := pow_add q v kd
  unfold pfdPrimalWeight pfdDualWeight
  change edgeProductCount p m o * q ^ k * q ^ (m + 1) =
    (p / (1 - dualParam p q)) ^ m * q ^ v *
      (edgeProductCount (dualParam p q) m (m - o) * q ^ kd)
  calc
    edgeProductCount p m o * q ^ k * q ^ (m + 1) =
        (edgeProductCount p m o * q ^ m) * (q ^ k * q) := by
      rw [pow_succ]
      ring
    _ = ((p / (1 - dualParam p q)) ^ m * q ^ o *
          edgeProductCount (dualParam p q) m (m - o)) * (q ^ k * q) := by
      rw [hedge]
    _ = (p / (1 - dualParam p q)) ^ m *
          edgeProductCount (dualParam p q) m (m - o) * (q ^ o * q ^ k * q) := by
      ring
    _ = (p / (1 - dualParam p q)) ^ m * q ^ v *
          (edgeProductCount (dualParam p q) m (m - o) * q ^ kd) := by
      rw [hpow]
      ring


theorem pfd_openSub_edge_ncard {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (omega : ConfigSpace (Sym2 V)) :
    (FK.openSub G omega).edgeSet.ncard = FK.openCount G omega := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  unfold FK.openCount
  congr 1
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [Set.mem_toFinset, SimpleGraph.mem_edgeSet, FK.openSub_adj,
        Finset.mem_filter, SimpleGraph.mem_edgeFinset]


theorem pfd_primalWeight_openSub (P : PlanarZ2Subgraph)
    (p q : ℝ) (omega : ConfigSpace (Sym2 P.V)) :
    pfdPrimalWeight P p q (FK.openSub P.G omega) = FK.fkWeight P.G p q omega := by
  unfold pfdPrimalWeight FK.fkWeight
  rw [pfd_openSub_edge_ncard]
  rw [dlt_edgeProduct_eq_count]
  unfold FK.numClusters
  rw [Nat.card_eq_fintype_card]


theorem pfd_fkWeight_duality (P : PlanarZ2Subgraph)
    (omega : ConfigSpace (Sym2 P.V)) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.fkWeight P.G p q omega * q ^ (P.G.edgeFinset.card + 1) =
      (p / (1 - dualParam p q)) ^ P.G.edgeFinset.card * q ^ Nat.card P.V *
        pfdDualWeight P (dualParam p q) q (FK.openSub P.G omega) := by
  rw [← pfd_primalWeight_openSub P p q omega]
  exact pfd_weight_duality P (FK.openSub P.G omega) (FK.openSub_le P.G omega) hp hp1 hq


end BeffaraDC
end StatMech
