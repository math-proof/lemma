/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Def.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part8
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

theorem triHexTorus_euler (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (TorusSite L)) :
    (Nat.card (TorusSite L) : ℤ) - K.edgeSet.ncard +
        triHexTorusFaceCount L K =
      Nat.card K.ConnectedComponent + 1 - triHexTorusDefect L K := by
  unfold triHexTorusDefect
  ring

theorem mem_openSub_edgeSet_iff
    {V : Type*} (G : SimpleGraph V) (omega : ConfigSpace (Sym2 V))
    {e : Sym2 V} (he : e ∈ G.edgeSet) :
    e ∈ (FK.openSub G omega).edgeSet ↔ omega e = true := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet, FK.openSub_adj]
      simpa only [SimpleGraph.mem_edgeSet] using and_iff_right he

theorem triHexTorusFaceCount_openSub (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (Sym2 (TorusSite L))) :
    triHexTorusFaceCount L (FK.openSub (triangularTorusGraph L) omega) =
      FK.numClusters (hexagonalTorusGraph L) (triHexTorusDualConfig L omega) := by
  classical
  have hcfg : triHexTorusDualConfig L
        (graphEdgeConfig (FK.openSub (triangularTorusGraph L) omega)) =
      triHexTorusDualConfig L omega := by
    funext e
    by_cases he : e ∈ (hexagonalTorusGraph L).edgeSet
    · have hpSet : triHexTorusPrimalOfDualEdge L e ∈
          (triangularTorusGraph L).edgeSet := by
        simp only [triHexTorusPrimalOfDualEdge, dif_pos he]
        exact ((triHexTorusDualEdgeEquiv L).symm ⟨e, he⟩).2
      have hopen : triHexTorusPrimalOfDualEdge L e ∈
            (FK.openSub (triangularTorusGraph L) omega).edgeSet ↔
          omega (triHexTorusPrimalOfDualEdge L e) = true := by
        exact mem_openSub_edgeSet_iff (triangularTorusGraph L) omega hpSet
      unfold triHexTorusDualConfig
      simp only [dif_pos he]
      cases homega : omega (triHexTorusPrimalOfDualEdge L e)
      · have hclosed : triHexTorusPrimalOfDualEdge L e ∉
            (FK.openSub (triangularTorusGraph L) omega).edgeSet := by
          rw [hopen, homega]
          simp
        simp [graphEdgeConfig, hclosed]
      · have hopen' : triHexTorusPrimalOfDualEdge L e ∈
            (FK.openSub (triangularTorusGraph L) omega).edgeSet := by
          rw [hopen, homega]
        simp [graphEdgeConfig, hopen']
    · unfold triHexTorusDualConfig
      simp [he]
  unfold triHexTorusFaceCount FK.numClusters
  have hg := congrArg (FK.openSub (hexagonalTorusGraph L)) hcfg
  calc
    Nat.card (FK.openSub (hexagonalTorusGraph L)
        (triHexTorusDualConfig L
          (graphEdgeConfig (FK.openSub (triangularTorusGraph L) omega)))).ConnectedComponent =
        Nat.card (FK.openSub (hexagonalTorusGraph L)
          (triHexTorusDualConfig L omega)).ConnectedComponent := by
      exact congrArg (fun G : SimpleGraph (HexTorusVertex L) =>
        Nat.card G.ConnectedComponent) hg
    _ = Fintype.card (FK.openSub (hexagonalTorusGraph L)
        (triHexTorusDualConfig L omega)).ConnectedComponent :=
      Nat.card_eq_fintype_card

theorem triHexTorus_openSub_edge_ncard
    {V : Type*} [Fintype V]
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

theorem triHexTorus_edge_card (L : ℕ) [Fact (2 < L)] :
    (triangularTorusGraph L).edgeFinset.card =
      (hexagonalTorusGraph L).edgeFinset.card := by
  simpa [SimpleGraph.edgeFinset] using
    Fintype.card_congr (triHexTorusDualEdgeEquiv L)


theorem triHexTorus_fkWeight_duality_signed (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (Sym2 (TorusSite L)))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.fkWeight (triangularTorusGraph L) p q omega *
        q ^ ((triangularTorusGraph L).edgeFinset.card + 1) =
      (p / (1 - BeffaraDC.dualParam p q)) ^
          (triangularTorusGraph L).edgeFinset.card *
        q ^ Nat.card (TorusSite L) *
        FK.fkWeight (hexagonalTorusGraph L)
          (BeffaraDC.dualParam p q) q (triHexTorusDualConfig L omega) *
        q ^ triHexTorusDefect L
          (FK.openSub (triangularTorusGraph L) omega) := by
  let m := (triangularTorusGraph L).edgeFinset.card
  let o := FK.openCount (triangularTorusGraph L) omega
  let k := Nat.card (FK.openSub (triangularTorusGraph L) omega).ConnectedComponent
  let kd := Nat.card (FK.openSub (hexagonalTorusGraph L)
    (triHexTorusDualConfig L omega)).ConnectedComponent
  let v := Nat.card (TorusSite L)
  let d := triHexTorusDefect L (FK.openSub (triangularTorusGraph L) omega)
  have hom : o ≤ m := Finset.card_filter_le _ _
  have hedge := BeffaraDC.dlt_edgeProduct_duality hp hp1 hq m o hom
  have heuler : ((o + k + 1 : ℕ) : ℤ) = ((v + kd : ℕ) : ℤ) + d := by
    have h := triHexTorus_euler L (FK.openSub (triangularTorusGraph L) omega)
    rw [triHexTorus_openSub_edge_ncard,
      triHexTorusFaceCount_openSub] at h
    unfold FK.numClusters at h
    rw [← Nat.card_eq_fintype_card] at h
    push_cast at h ⊢
    dsimp only [o, k, kd, v, d]
    linarith
  have hqne : q ≠ 0 := ne_of_gt hq
  have hpow : q ^ (o + k + 1) = q ^ (v + kd) * q ^ d := by
    rw [← zpow_natCast, ← zpow_natCast, heuler, zpow_add₀ hqne]
  unfold FK.fkWeight
  unfold FK.numClusters
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  rw [BeffaraDC.dlt_edgeProduct_eq_count,
    BeffaraDC.dlt_edgeProduct_eq_count]
  change BeffaraDC.edgeProductCount p m o * q ^ k * q ^ (m + 1) =
    (p / (1 - BeffaraDC.dualParam p q)) ^ m * q ^ v *
      (BeffaraDC.edgeProductCount (BeffaraDC.dualParam p q)
        (hexagonalTorusGraph L).edgeFinset.card
        (FK.openCount (hexagonalTorusGraph L) (triHexTorusDualConfig L omega)) *
          q ^ kd) * q ^ d
  rw [← triHexTorus_edge_card L, triHexTorus_dual_openCount,
    ← triHexTorus_edge_card L]
  change BeffaraDC.edgeProductCount p m o * q ^ k * q ^ (m + 1) =
    (p / (1 - BeffaraDC.dualParam p q)) ^ m * q ^ v *
      (BeffaraDC.edgeProductCount (BeffaraDC.dualParam p q) m (m - o) *
        q ^ kd) * q ^ d
  calc
    BeffaraDC.edgeProductCount p m o * q ^ k * q ^ (m + 1) =
        (BeffaraDC.edgeProductCount p m o * q ^ m) * (q ^ k * q) := by
      rw [pow_succ]
      ring
    _ = ((p / (1 - BeffaraDC.dualParam p q)) ^ m * q ^ o *
          BeffaraDC.edgeProductCount (BeffaraDC.dualParam p q) m (m - o)) *
          (q ^ k * q) := by rw [hedge]
    _ = (p / (1 - BeffaraDC.dualParam p q)) ^ m *
          BeffaraDC.edgeProductCount (BeffaraDC.dualParam p q) m (m - o) *
          q ^ (o + k + 1) := by
      rw [pow_add, pow_succ]
      ring
    _ = (p / (1 - BeffaraDC.dualParam p q)) ^ m *
          BeffaraDC.edgeProductCount (BeffaraDC.dualParam p q) m (m - o) *
          (q ^ (v + kd) * q ^ d) := by rw [hpow]
    _ = (p / (1 - BeffaraDC.dualParam p q)) ^ m * q ^ v *
          (BeffaraDC.edgeProductCount (BeffaraDC.dualParam p q) m (m - o) *
            q ^ kd) * q ^ d := by
      rw [pow_add]
      ring


end PeriodicPlanar
end FK
end StatMech
