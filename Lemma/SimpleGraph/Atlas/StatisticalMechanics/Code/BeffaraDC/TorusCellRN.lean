import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellRN.Part5
open SimpleGraph Set StatMech StatMech.BeffaraDC


/--
[torusAmbientConfigRestrict_extend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellRN.lean)
-/
@[path]
private lemma torusAmbientConfigRestrict_extend_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L} :
-- imply
  torusAmbientConfigRestrict L (torusAmbientConfigExtend L omega) = omega := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientConfigRestrict_extend L omega

/--
[torusAmbientConfigExtend_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellRN.lean)
-/
@[path]
private lemma torusAmbientConfigExtend_dual_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L} :
-- imply
  torusAmbientConfigExtend L (torusCellDualAmbientConfig L omega) = torusCellDualConfig L (torusAmbientConfigExtend L omega) := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientConfigExtend_dual L omega

/--
[torusAmbientFKWeight_duality_signed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellRN.lean)
-/
@[path]
private lemma torusAmbientFKWeight_duality_signed_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  torusAmbientFKWeight L p q omega * q ^ ((onsTorusGraph L).edgeFinset.card + 1) = (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card * q ^ Nat.card (ZMod L × ZMod L) * torusAmbientFKWeight L (dualParam p q) q (torusCellDualAmbientConfig L omega) * q ^ torusCellDefect L (FK.openSub (onsTorusGraph L) (torusAmbientConfigExtend L omega)) := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientFKWeight_duality_signed L omega hp hp1 hq

/--
[torusAmbientDefect_classified](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellRN.lean)
-/
@[path]
private lemma torusAmbientDefect_classified_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L} :
-- imply
  torusAmbientDefect L omega = 0 ∨ torusAmbientDefect L omega = 1 ∨ torusAmbientDefect L omega = 2 := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientDefect_classified L omega

/--
[torusAmbientDefect_add_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellRN.lean)
-/
@[path]
private lemma torusAmbientDefect_add_dual_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L} :
-- imply
  torusAmbientDefect L omega + torusAmbientDefect L (torusCellDualAmbientConfig L omega) = 2 := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientDefect_add_dual L omega

/--
[torusAmbientPartition_reindex_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellRN.lean)
-/
@[path]
private lemma torusAmbientPartition_reindex_dual_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ} :
-- imply
  (∑ omega : TorusAmbientConfig L, torusAmbientFKWeight L p q (torusCellDualAmbientConfig L omega)) = torusAmbientPartition L p q := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientPartition_reindex_dual L p q

/--
[selfDualPoint_odds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellRN.lean)
-/
@[path]
private lemma selfDualPoint_odds_eq
  {q : ℝ}
-- given
  (hq : 0 < q) :
-- imply
  selfDualPoint q / (1 - selfDualPoint q) = Real.sqrt q := by
-- proof
  apply StatMech.BeffaraDC.selfDualPoint_odds hq

/--
[torusAmbient_selfDual_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellRN.lean)
-/
@[path]
private lemma torusAmbient_selfDual_prefactor_eq
  {L : ℕ}
  [Fact (2 < L)]
  {q : ℝ}
-- given
  (hq : 0 < q) :
-- imply
  (selfDualPoint q / (1 - dualParam (selfDualPoint q) q)) ^ (onsTorusGraph L).edgeFinset.card * q ^ Nat.card (ZMod L × ZMod L) = q ^ (onsTorusGraph L).edgeFinset.card := by
-- proof
  apply StatMech.BeffaraDC.torusAmbient_selfDual_prefactor L hq

/--
[torusAmbientFKWeight_selfDual_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellRN.lean)
-/
@[path]
private lemma torusAmbientFKWeight_selfDual_relation_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L}
  {q : ℝ}
-- given
  (hq : 0 < q) :
-- imply
  torusAmbientFKWeight L (selfDualPoint q) q omega * q = torusAmbientFKWeight L (selfDualPoint q) q (torusCellDualAmbientConfig L omega) * q ^ torusAmbientDefect L omega := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientFKWeight_selfDual_relation L omega hq

/--
[torusAmbientFKWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellRN.lean)
-/
@[path]
private lemma torusAmbientFKWeight_pos_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < torusAmbientFKWeight L p q omega := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientFKWeight_pos L omega hp hp1 hq

/--
[torusAmbientPartition_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellRN.lean)
-/
@[path]
private lemma torusAmbientPartition_pos_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < torusAmbientPartition L p q := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientPartition_pos L hp hp1 hq

/--
[torusAmbientProbability_sum_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellRN.lean)
-/
@[path]
private lemma torusAmbientProbability_sum_one_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∑ omega : TorusAmbientConfig L, torusAmbientProbability L p q omega = 1 := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientProbability_sum_one L hp hp1 hq

/--
[torusAmbientProbability_ratio_eq_weight_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellRN.lean)
-/
@[path]
private lemma torusAmbientProbability_ratio_eq_weight_ratio_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  torusAmbientProbability L p q omega / torusAmbientProbability L p q (torusCellDualAmbientConfig L omega) = torusAmbientFKWeight L p q omega / torusAmbientFKWeight L p q (torusCellDualAmbientConfig L omega) := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientProbability_ratio_eq_weight_ratio L omega hp hp1 hq

/--
[torusAmbientProbability_selfDual_ratio_eq_zpow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellRN.lean)
-/
@[path]
private lemma torusAmbientProbability_selfDual_ratio_eq_zpow_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L}
  {q : ℝ}
-- given
  (hq : 0 < q) :
-- imply
  torusAmbientProbability L (selfDualPoint q) q omega / torusAmbientProbability L (selfDualPoint q) q (torusCellDualAmbientConfig L omega) = q ^ (torusAmbientDefect L omega - 1) := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientProbability_selfDual_ratio_eq_zpow L omega hq

/--
[torusAmbientProbability_selfDual_ratio_values](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellRN.lean)
-/
@[path]
private lemma torusAmbientProbability_selfDual_ratio_values_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L}
  {q : ℝ}
-- given
  (hq : 0 < q) :
-- imply
  let ratio := torusAmbientProbability L (selfDualPoint q) q omega / torusAmbientProbability L (selfDualPoint q) q (torusCellDualAmbientConfig L omega) ratio = q⁻¹ ∨ ratio = 1 ∨ ratio = q := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientProbability_selfDual_ratio_values L omega hq

/--
[torusAmbientProbability_selfDual_ratio_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellRN.lean)
-/
@[path]
private lemma torusAmbientProbability_selfDual_ratio_mem_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L}
  {q : ℝ}
-- given
  (hq1 : 1 ≤ q) :
-- imply
  let ratio := torusAmbientProbability L (selfDualPoint q) q omega / torusAmbientProbability L (selfDualPoint q) q (torusCellDualAmbientConfig L omega) q⁻¹ ≤ ratio ∧ ratio ≤ q := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientProbability_selfDual_ratio_mem L omega hq1


-- created on 2026-10-23
