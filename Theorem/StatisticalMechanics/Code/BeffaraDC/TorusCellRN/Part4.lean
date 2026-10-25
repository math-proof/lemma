/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellRN.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellFKDuality
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellDefectClassify.Part3
import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
import Def.StatisticalMechanics.Code.BeffaraDC.TorusCellRN.Part4
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Onsager


theorem torusAmbientPartition_reindex_dual (L : ℕ) [Fact (2 < L)]
    (p q : ℝ) :
    (∑ omega : TorusAmbientConfig L,
        torusAmbientFKWeight L p q (torusCellDualAmbientConfig L omega)) =
      torusAmbientPartition L p q := by
  unfold torusAmbientPartition
  exact Equiv.sum_comp (torusCellDualAmbientConfigEquiv L)
    (torusAmbientFKWeight L p q)


theorem selfDualPoint_odds {q : ℝ} (hq : 0 < q) :
    selfDualPoint q / (1 - selfDualPoint q) = Real.sqrt q := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  unfold selfDualPoint
  field_simp
  ring


theorem torusAmbient_selfDual_prefactor (L : ℕ) [Fact (2 < L)]
    {q : ℝ} (hq : 0 < q) :
    (selfDualPoint q /
          (1 - dualParam (selfDualPoint q) q)) ^
        (onsTorusGraph L).edgeFinset.card *
      q ^ Nat.card (ZMod L × ZMod L) =
        q ^ (onsTorusGraph L).edgeFinset.card := by
  rw [selfDualPoint_is_fixed hq, selfDualPoint_odds hq]
  have hedge : (onsTorusGraph L).edgeFinset.card = 2 * L ^ 2 :=
    onsTorus_card_edges L
  have hvert : Nat.card (ZMod L × ZMod L) = L ^ 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card]
    ring
  rw [hedge, hvert, pow_mul, Real.sq_sqrt hq.le, ← pow_add]
  congr 2
  omega


theorem torusAmbientFKWeight_selfDual_relation
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L)
    {q : ℝ} (hq : 0 < q) :
    torusAmbientFKWeight L (selfDualPoint q) q omega * q =
      torusAmbientFKWeight L (selfDualPoint q) q
          (torusCellDualAmbientConfig L omega) *
        q ^ torusAmbientDefect L omega := by
  obtain ⟨hp, hp1⟩ := selfDualPoint_mem_Ioo hq
  have h := torusAmbientFKWeight_duality_signed L omega hp hp1 hq
  have hpref := torusAmbient_selfDual_prefactor L hq
  rw [selfDualPoint_is_fixed hq] at h hpref
  rw [hpref] at h
  rw [pow_succ] at h
  have hqm : q ^ (onsTorusGraph L).edgeFinset.card ≠ 0 :=
    ne_of_gt (pow_pos hq _)
  apply mul_left_cancel₀ hqm
  calc
    q ^ (onsTorusGraph L).edgeFinset.card *
        (torusAmbientFKWeight L (selfDualPoint q) q omega * q) =
      torusAmbientFKWeight L (selfDualPoint q) q omega *
        (q ^ (onsTorusGraph L).edgeFinset.card * q) := by ring
    _ = q ^ (onsTorusGraph L).edgeFinset.card *
        (torusAmbientFKWeight L (selfDualPoint q) q
          (torusCellDualAmbientConfig L omega) *
          q ^ torusAmbientDefect L omega) := by
      simpa only [torusAmbientDefect, mul_assoc] using h


theorem torusAmbientFKWeight_pos (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < torusAmbientFKWeight L p q omega := by
  unfold torusAmbientFKWeight
  exact FK.fkWeight_pos (onsTorusGraph L) hp hp1 hq _


theorem torusAmbientPartition_pos (L : ℕ) [Fact (2 < L)]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < torusAmbientPartition L p q := by
  unfold torusAmbientPartition
  exact Finset.sum_pos
    (fun omega _ => torusAmbientFKWeight_pos L omega hp hp1 hq)
    Finset.univ_nonempty


end StatMech.BeffaraDC
