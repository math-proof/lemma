/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteActiveDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Def.StatisticalMechanics.Code.FK.FiniteActiveDuality.Part3
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.FK

open Lattice

noncomputable section

variable {V W : Type*} [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph V) (H : SimpleGraph W)
  [DecidableRel G.Adj] [DecidableRel H.Adj]


theorem active_free_wired_weight_duality
    (boundary : W → Prop) [DecidablePred boundary]
    (edgeDual : G.edgeSet ≃ H.edgeSet)
    (hEuler : ActiveFreeWiredEulerIdentity G H boundary edgeDual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (omega : ConfigSpace G.edgeSet) :
    activeWeight G (fun _ => p) q omega *
        q ^ (Fintype.card G.edgeSet + 1) =
      (p / (1 - BeffaraDC.dualParam p q)) ^
          Fintype.card G.edgeSet * q ^ Fintype.card V *
        PeriodicPlanar.wiredActiveWeight H boundary
          (BeffaraDC.dualParam p q) q
          (activeDualConfig G H edgeDual omega) := by
  let m := Fintype.card G.edgeSet
  let o := activeOpenCount G omega
  let k := numClusters G (extendActive G omega)
  let eta := activeDualConfig G H edgeDual omega
  let kd := numClustersWired H boundary (extendActive H eta)
  let v := Fintype.card V
  have hom : o ≤ m := Fintype.card_subtype_le _
  have hedge := BeffaraDC.dlt_edgeProduct_duality hp hp1 hq m o hom
  have hedgeCard : Fintype.card H.edgeSet = m := by
    simpa only [m] using (Fintype.card_congr edgeDual).symm
  have hopenDual : activeOpenCount H eta = m - o := by
    dsimp only [eta, m, o]
    exact activeOpenCount_dualConfig G H edgeDual omega
  have heuler : v + kd = o + k + 1 := hEuler omega
  have hpow : q ^ o * q ^ k * q = q ^ v * q ^ kd := by
    calc
      q ^ o * q ^ k * q = q ^ (o + k + 1) := by
        rw [← pow_add, ← pow_succ]
      _ = q ^ (v + kd) := congrArg (q ^ ·) heuler.symm
      _ = q ^ v * q ^ kd := pow_add q v kd
  rw [activeWeight_eq_count G p q omega,
    wiredActiveWeight_eq_count H boundary
      (BeffaraDC.dualParam p q) q eta]
  rw [hedgeCard, hopenDual]
  change BeffaraDC.edgeProductCount p m o * q ^ k * q ^ (m + 1) =
    (p / (1 - BeffaraDC.dualParam p q)) ^ m * q ^ v *
      (BeffaraDC.edgeProductCount (BeffaraDC.dualParam p q) m (m - o) *
        q ^ kd)
  calc
    BeffaraDC.edgeProductCount p m o * q ^ k * q ^ (m + 1) =
        (BeffaraDC.edgeProductCount p m o * q ^ m) *
          (q ^ k * q) := by
      rw [pow_succ]
      ring
    _ = ((p / (1 - BeffaraDC.dualParam p q)) ^ m * q ^ o *
          BeffaraDC.edgeProductCount (BeffaraDC.dualParam p q) m (m - o)) *
          (q ^ k * q) := by
      rw [hedge]
    _ = (p / (1 - BeffaraDC.dualParam p q)) ^ m *
          BeffaraDC.edgeProductCount (BeffaraDC.dualParam p q) m (m - o) *
          (q ^ o * q ^ k * q) := by ring
    _ = (p / (1 - BeffaraDC.dualParam p q)) ^ m * q ^ v *
          (BeffaraDC.edgeProductCount (BeffaraDC.dualParam p q) m (m - o) *
            q ^ kd) := by
      rw [hpow]
      ring


theorem active_free_wired_prob_duality
    (boundary : W → Prop) [DecidablePred boundary]
    (edgeDual : G.edgeSet ≃ H.edgeSet)
    (hEuler : ActiveFreeWiredEulerIdentity G H boundary edgeDual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (omega : ConfigSpace G.edgeSet) :
    activeProb G (fun _ => p) q omega =
      PeriodicPlanar.wiredActiveWeight H boundary
          (BeffaraDC.dualParam p q) q
          (activeDualConfig G H edgeDual omega) /
        PeriodicPlanar.wiredActiveZ H boundary
          (BeffaraDC.dualParam p q) q := by
  let A : Real := q ^ (Fintype.card G.edgeSet + 1)
  let B : Real :=
    (p / (1 - BeffaraDC.dualParam p q)) ^ Fintype.card G.edgeSet *
      q ^ Fintype.card V
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hpDual := BeffaraDC.dualParam_mem_Ioo hp hp1 hq
  have hB : 0 < B := by
    dsimp only [B]
    exact mul_pos (pow_pos (div_pos hp (sub_pos.mpr hpDual.2)) _)
      (pow_pos hq _)
  have hpoint :
      activeWeight G (fun _ => p) q omega * A =
        B * PeriodicPlanar.wiredActiveWeight H boundary
          (BeffaraDC.dualParam p q) q
          (activeDualConfig G H edgeDual omega) := by
    exact active_free_wired_weight_duality G H boundary edgeDual hEuler
      hp hp1 hq omega
  have hsum :
      activeZ G (fun _ => p) q * A =
        B * PeriodicPlanar.wiredActiveZ H boundary
          (BeffaraDC.dualParam p q) q := by
    calc
      activeZ G (fun _ => p) q * A =
          ∑ omega : ConfigSpace G.edgeSet,
            activeWeight G (fun _ => p) q omega * A := by
        unfold activeZ
        rw [Finset.sum_mul]
      _ = ∑ omega : ConfigSpace G.edgeSet,
          B * PeriodicPlanar.wiredActiveWeight H boundary
            (BeffaraDC.dualParam p q) q
            (activeDualConfig G H edgeDual omega) := by
        apply Finset.sum_congr rfl
        intro eta _
        exact active_free_wired_weight_duality G H boundary edgeDual hEuler
          hp hp1 hq eta
      _ = B * ∑ eta : ConfigSpace H.edgeSet,
          PeriodicPlanar.wiredActiveWeight H boundary
            (BeffaraDC.dualParam p q) q eta := by
        rw [← Finset.mul_sum]
        congr 1
        exact Equiv.sum_comp (activeDualConfig G H edgeDual)
          (fun eta => PeriodicPlanar.wiredActiveWeight H boundary
            (BeffaraDC.dualParam p q) q eta)
      _ = B * PeriodicPlanar.wiredActiveZ H boundary
          (BeffaraDC.dualParam p q) q := by
        rfl
  have hZfree : 0 < activeZ G (fun _ => p) q :=
    activeZ_pos G (fun _ => hp) (fun _ => hp1) hq
  have hZwired : 0 < PeriodicPlanar.wiredActiveZ H boundary
      (BeffaraDC.dualParam p q) q := by
    unfold PeriodicPlanar.wiredActiveZ
    exact Finset.sum_pos
      (fun eta _ => wiredFkWeight_pos H boundary hpDual.1 hpDual.2 hq
        (extendActive H eta))
      Finset.univ_nonempty
  have hw : activeWeight G (fun _ => p) q omega =
      (B / A) * PeriodicPlanar.wiredActiveWeight H boundary
        (BeffaraDC.dualParam p q) q
        (activeDualConfig G H edgeDual omega) := by
    calc
      activeWeight G (fun _ => p) q omega =
          (B * PeriodicPlanar.wiredActiveWeight H boundary
            (BeffaraDC.dualParam p q) q
            (activeDualConfig G H edgeDual omega)) / A :=
        (eq_div_iff hA.ne').2 hpoint
      _ = (B / A) * PeriodicPlanar.wiredActiveWeight H boundary
          (BeffaraDC.dualParam p q) q
          (activeDualConfig G H edgeDual omega) := by ring
  have hZ : activeZ G (fun _ => p) q =
      (B / A) * PeriodicPlanar.wiredActiveZ H boundary
        (BeffaraDC.dualParam p q) q := by
    calc
      activeZ G (fun _ => p) q =
          (B * PeriodicPlanar.wiredActiveZ H boundary
            (BeffaraDC.dualParam p q) q) / A :=
        (eq_div_iff hA.ne').2 hsum
      _ = (B / A) * PeriodicPlanar.wiredActiveZ H boundary
          (BeffaraDC.dualParam p q) q := by ring
  unfold activeProb
  rw [hw, hZ]
  field_simp [hA.ne', hB.ne', hZfree.ne', hZwired.ne']

end
end StatMech.FK
