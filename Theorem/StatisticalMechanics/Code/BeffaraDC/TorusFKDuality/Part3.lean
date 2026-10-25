/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusFKDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusGeometricEuler.Part3
import Def.StatisticalMechanics.Code.BeffaraDC.TorusFKDuality.Part3
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Onsager


theorem torus_weight_q_sandwich (L : ℕ) [Fact (2 < L)]
    (hclass : TorusDefectClassified L)
    (K : SimpleGraph (ZMod L × ZMod L)) (hK : K ≤ onsTorusGraph L)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) :
    let primal := torusPrimalWeight L p q K *
      q ^ ((onsTorusGraph L).edgeFinset.card + 1)
    let dual := (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
      q ^ Nat.card (ZMod L × ZMod L) * q *
      torusDualWeight L (dualParam p q) q K
    primal ≤ q * dual ∧ dual ≤ q * primal := by
  have hq : 0 < q := lt_of_lt_of_le one_pos hq1
  have hps0 : 0 < dualParam p q := dualParam_pos hp hp1 hq
  have hps1 : dualParam p q < 1 := dualParam_lt_one hp hp1 hq
  have hP0 : 0 ≤ torusPrimalWeight L p q K *
      q ^ ((onsTorusGraph L).edgeFinset.card + 1) :=
    (mul_pos (torusPrimalWeight_pos L K hp hp1 hq) (pow_pos hq _)).le
  have hD0 : 0 ≤ (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
      q ^ Nat.card (ZMod L × ZMod L) * q *
      torusDualWeight L (dualParam p q) q K := by
    have hden : 0 < 1 - dualParam p q := by linarith
    exact (mul_pos
      (mul_pos (mul_pos (pow_pos (div_pos hp hden) _) (pow_pos hq _)) hq)
      (torusDualWeight_pos L K hps0 hps1 hq)).le
  dsimp only
  rcases hclass K hK with hδ | hδ | hδ
  · have heq := torus_weight_duality_of_defect L K hK hp hp1 hq 0 hδ
    simp only [pow_zero, mul_one] at heq
    have hrel : (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
        q ^ Nat.card (ZMod L × ZMod L) * q *
        torusDualWeight L (dualParam p q) q K =
        q * (torusPrimalWeight L p q K *
          q ^ ((onsTorusGraph L).edgeFinset.card + 1)) := by
      rw [heq]
      ring
    constructor
    · rw [hrel]
      nlinarith
    · rw [hrel]
  · have heq := torus_weight_duality_of_defect L K hK hp hp1 hq 1 hδ
    simp only [pow_one] at heq
    have heq' : torusPrimalWeight L p q K *
        q ^ ((onsTorusGraph L).edgeFinset.card + 1) =
        (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
          q ^ Nat.card (ZMod L × ZMod L) * q *
          torusDualWeight L (dualParam p q) q K := by
      calc
        _ = (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
            q ^ Nat.card (ZMod L × ZMod L) *
            torusDualWeight L (dualParam p q) q K * q := heq
        _ = _ := by ring
    constructor
    · rw [heq']
      nlinarith
    · rw [heq']
      nlinarith
  · have heq := torus_weight_duality_of_defect L K hK hp hp1 hq 2 hδ
    simp only [pow_two] at heq
    have heq' : torusPrimalWeight L p q K *
        q ^ ((onsTorusGraph L).edgeFinset.card + 1) =
        q * ((p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
          q ^ Nat.card (ZMod L × ZMod L) * q *
          torusDualWeight L (dualParam p q) q K) := by
      calc
        _ = (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
            q ^ Nat.card (ZMod L × ZMod L) *
            torusDualWeight L (dualParam p q) q K * (q * q) := heq
        _ = _ := by ring
    constructor
    · rw [heq']
    · rw [heq']
      nlinarith


theorem torus_normalized_event_comparison (L : ℕ) [Fact (2 < L)]
    (hclass : TorusDefectClassified L) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q)
    (A : Finset (ConfigSpace (Sym2 (ZMod L × ZMod L)))) :
    let w := fun ω : ConfigSpace (Sym2 (ZMod L × ZMod L)) =>
      torusPrimalWeight L p q (FK.openSub (onsTorusGraph L) ω) *
        q ^ ((onsTorusGraph L).edgeFinset.card + 1)
    let w' := fun ω : ConfigSpace (Sym2 (ZMod L × ZMod L)) =>
      (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
        q ^ Nat.card (ZMod L × ZMod L) * q *
        torusDualWeight L (dualParam p q) q (FK.openSub (onsTorusGraph L) ω)
    (∑ ω ∈ A, w ω) / (∑ ω, w ω) ≤
      q ^ 2 * ((∑ ω ∈ A, w' ω) / (∑ ω, w' ω)) := by
  have hq : 0 < q := lt_of_lt_of_le one_pos hq1
  have hps0 : 0 < dualParam p q := dualParam_pos hp hp1 hq
  have hps1 : dualParam p q < 1 := dualParam_lt_one hp hp1 hq
  dsimp only
  apply dlt_rn_sandwich
      (fun ω : ConfigSpace (Sym2 (ZMod L × ZMod L)) =>
        torusPrimalWeight L p q (FK.openSub (onsTorusGraph L) ω) *
          q ^ ((onsTorusGraph L).edgeFinset.card + 1))
      (fun ω : ConfigSpace (Sym2 (ZMod L × ZMod L)) =>
        (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
          q ^ Nat.card (ZMod L × ZMod L) * q *
          torusDualWeight L (dualParam p q) q (FK.openSub (onsTorusGraph L) ω))
      q hq1 1
  · intro ω
    have hden : 0 < 1 - dualParam p q := by linarith
    exact mul_pos
      (mul_pos (mul_pos (pow_pos (div_pos hp hden) _) (pow_pos hq _)) hq)
      (torusDualWeight_pos L (FK.openSub (onsTorusGraph L) ω) hps0 hps1 hq)
  · intro ω
    exact mul_pos
      (torusPrimalWeight_pos L (FK.openSub (onsTorusGraph L) ω) hp hp1 hq)
      (pow_pos hq _)
  · intro ω
    have hs := torus_weight_q_sandwich L hclass
      (FK.openSub (onsTorusGraph L) ω) (FK.openSub_le (onsTorusGraph L) ω)
      hp hp1 hq1
    dsimp only at hs
    rw [zpow_neg, zpow_natCast, pow_one]
    exact (inv_mul_le_iff₀ hq).2 hs.2
  · intro ω
    have hs := torus_weight_q_sandwich L hclass
      (FK.openSub (onsTorusGraph L) ω) (FK.openSub_le (onsTorusGraph L) ω)
      hp hp1 hq1
    dsimp only at hs
    simpa using hs.1

end StatMech.BeffaraDC
