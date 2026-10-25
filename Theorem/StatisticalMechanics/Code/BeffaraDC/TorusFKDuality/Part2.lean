/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusFKDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusGeometricEuler.Part3
import Def.StatisticalMechanics.Code.BeffaraDC.TorusFKDuality.Part2
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Onsager


theorem torus_openSub_edge_ncard {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ω : ConfigSpace (Sym2 V)) :
    (FK.openSub G ω).edgeSet.ncard = FK.openCount G ω := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  unfold FK.openCount
  congr 1
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [Set.mem_toFinset, SimpleGraph.mem_edgeSet, FK.openSub_adj,
        Finset.mem_filter, SimpleGraph.mem_edgeFinset]


theorem torus_primalWeight_openSub (L : ℕ) [Fact (2 < L)] (p q : ℝ)
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    torusPrimalWeight L p q (FK.openSub (onsTorusGraph L) ω) =
      FK.fkWeight (onsTorusGraph L) p q ω := by
  unfold torusPrimalWeight FK.fkWeight
  rw [torus_openSub_edge_ncard, dlt_edgeProduct_eq_count]
  unfold FK.numClusters
  rw [Nat.card_eq_fintype_card]


theorem torus_dualWeight_openSub (L : ℕ) [Fact (2 < L)] (p q : ℝ)
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    torusDualWeight L p q (FK.openSub (onsTorusGraph L) ω) =
      FK.fkWeight (onsTorusGraph L) p q (torusDualConfig L ω) := by
  unfold torusDualWeight FK.fkWeight
  rw [torus_openSub_edge_ncard, ← torus_dual_openCount,
    ← dlt_edgeProduct_eq_count, torus_numClusters_dualConfig]

theorem torusPrimalWeight_pos (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (ZMod L × ZMod L)) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < torusPrimalWeight L p q K := by
  unfold torusPrimalWeight edgeProductCount
  have h1p : 0 < 1 - p := by linarith
  positivity

theorem torusDualWeight_pos (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (ZMod L × ZMod L)) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < torusDualWeight L p q K := by
  unfold torusDualWeight edgeProductCount
  have h1p : 0 < 1 - p := by linarith
  positivity


theorem torus_subgraph_edgeCount_le (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (ZMod L × ZMod L)) (hK : K ≤ onsTorusGraph L) :
    K.edgeSet.ncard ≤ (onsTorusGraph L).edgeFinset.card := by
  have hset : K.edgeSet ⊆ (onsTorusGraph L).edgeSet := SimpleGraph.edgeSet_mono hK
  have hn := Set.ncard_le_ncard hset (Set.toFinite (onsTorusGraph L).edgeSet)
  simpa only [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card'] using hn


theorem torus_clusterEuler_signed (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (ZMod L × ZMod L)) :
    ((K.edgeSet.ncard + Nat.card K.ConnectedComponent + 1 : ℕ) : ℤ) =
      ((Nat.card (ZMod L × ZMod L) + torusGeometricFaceCount L K : ℕ) : ℤ) +
        torusGeometricDefect L K := by
  have h := geometric_euler_torus L K
  push_cast at h ⊢
  linarith


theorem torus_weight_duality_signed (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (ZMod L × ZMod L)) (hK : K ≤ onsTorusGraph L)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    torusPrimalWeight L p q K * q ^ ((onsTorusGraph L).edgeFinset.card + 1) =
      (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
        q ^ Nat.card (ZMod L × ZMod L) *
        torusDualWeight L (dualParam p q) q K *
        q ^ torusGeometricDefect L K := by
  let m := (onsTorusGraph L).edgeFinset.card
  let o := K.edgeSet.ncard
  let k := Nat.card K.ConnectedComponent
  let f := torusGeometricFaceCount L K
  let v := Nat.card (ZMod L × ZMod L)
  let d := torusGeometricDefect L K
  have hom : o ≤ m := torus_subgraph_edgeCount_le L K hK
  have hedge := dlt_edgeProduct_duality hp hp1 hq m o hom
  have heuler : ((o + k + 1 : ℕ) : ℤ) = ((v + f : ℕ) : ℤ) + d := by
    simpa only [o, k, v, f, d] using torus_clusterEuler_signed L K
  have hqne : q ≠ 0 := ne_of_gt hq
  have hpow : q ^ (o + k + 1) = q ^ (v + f) * q ^ d := by
    rw [← zpow_natCast, ← zpow_natCast]
    rw [heuler, zpow_add₀ hqne]
  unfold torusPrimalWeight torusDualWeight
  change edgeProductCount p m o * q ^ k * q ^ (m + 1) =
    (p / (1 - dualParam p q)) ^ m * q ^ v *
      (edgeProductCount (dualParam p q) m (m - o) * q ^ f) * q ^ d
  calc
    edgeProductCount p m o * q ^ k * q ^ (m + 1) =
        (edgeProductCount p m o * q ^ m) * (q ^ k * q) := by
      rw [pow_succ]
      ring
    _ = ((p / (1 - dualParam p q)) ^ m * q ^ o *
          edgeProductCount (dualParam p q) m (m - o)) * (q ^ k * q) := by
      rw [hedge]
    _ = (p / (1 - dualParam p q)) ^ m *
          edgeProductCount (dualParam p q) m (m - o) * q ^ (o + k + 1) := by
      rw [pow_add, pow_succ]
      ring
    _ = (p / (1 - dualParam p q)) ^ m *
          edgeProductCount (dualParam p q) m (m - o) * (q ^ (v + f) * q ^ d) := by
      rw [hpow]
    _ = (p / (1 - dualParam p q)) ^ m * q ^ v *
          (edgeProductCount (dualParam p q) m (m - o) * q ^ f) * q ^ d := by
      rw [pow_add]
      ring


theorem torus_fkWeight_duality_signed (L : ℕ) [Fact (2 < L)]
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L)))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.fkWeight (onsTorusGraph L) p q ω *
        q ^ ((onsTorusGraph L).edgeFinset.card + 1) =
      (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
        q ^ Nat.card (ZMod L × ZMod L) *
        FK.fkWeight (onsTorusGraph L) (dualParam p q) q
          (torusDualConfig L ω) *
        q ^ torusGeometricDefect L (FK.openSub (onsTorusGraph L) ω) := by
  rw [← torus_primalWeight_openSub L p q ω,
    ← torus_dualWeight_openSub L (dualParam p q) q ω]
  exact torus_weight_duality_signed L (FK.openSub (onsTorusGraph L) ω)
    (FK.openSub_le (onsTorusGraph L) ω) hp hp1 hq


theorem torus_weight_duality_of_defect (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (ZMod L × ZMod L)) (hK : K ≤ onsTorusGraph L)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (δ : ℕ)
    (hδ : torusGeometricDefect L K = δ) :
    torusPrimalWeight L p q K * q ^ ((onsTorusGraph L).edgeFinset.card + 1) =
      (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
        q ^ Nat.card (ZMod L × ZMod L) *
        torusDualWeight L (dualParam p q) q K * q ^ δ := by
  rw [torus_weight_duality_signed L K hK hp hp1 hq, hδ, zpow_natCast]


end StatMech.BeffaraDC
