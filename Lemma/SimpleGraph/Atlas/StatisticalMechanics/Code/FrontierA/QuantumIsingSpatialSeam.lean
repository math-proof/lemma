import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.QuantumIsingSpatialSeam
open StatMech StatMech.FrontierA


/--
[quantumIsingChainInteraction_succ_eq_open_add_seam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma quantumIsingChainInteraction_succ_eq_open_add_seam_eq
  {L : Nat}
  {sigma : QuantumIsingChainConfig (L + 1)} :
-- imply
  quantumIsingChainInteraction (L + 1) sigma = quantumIsingOpenChainInteraction L sigma + quantumIsingSpinSign (sigma (Fin.last L)) * quantumIsingSpinSign (sigma 0) := by
-- proof
  apply StatMech.FrontierA.quantumIsingChainInteraction_succ_eq_open_add_seam L sigma

/--
[quantumIsingOpenChainInteraction_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma quantumIsingOpenChainInteraction_add_eq
  {L M : Nat}
  {sigma : QuantumIsingChainConfig (L + M + 2)} :
-- imply
  quantumIsingOpenChainInteraction (L + M + 1) sigma = quantumIsingOpenChainInteraction L (quantumIsingLeftSpatialBlock L M sigma) + quantumIsingSpinSign ((quantumIsingLeftSpatialBlock L M sigma) (Fin.last L)) * quantumIsingSpinSign ((quantumIsingRightSpatialBlock L M sigma) 0) + quantumIsingOpenChainInteraction M (quantumIsingRightSpatialBlock L M sigma) := by
-- proof
  apply StatMech.FrontierA.quantumIsingOpenChainInteraction_add L M sigma

/--
[abs_quantumIsingChainInteraction_sub_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma abs_quantumIsingChainInteraction_sub_open_eq
  {L : Nat}
  {sigma : QuantumIsingChainConfig (L + 1)} :
-- imply
  |quantumIsingChainInteraction (L + 1) sigma - quantumIsingOpenChainInteraction L sigma| = 1 := by
-- proof
  apply StatMech.FrontierA.abs_quantumIsingChainInteraction_sub_open L sigma

/--
[quantumIsingSpatialTrotterWeight_le_exp_mul_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma quantumIsingSpatialTrotterWeight_le_exp_mul_open_eq
  {beta : Real}
  {n L : Nat}
  {sigma : QuantumIsingChainConfig (L + 1)}
-- given
  (hn : n ≠ 0)
  (hbeta : 0 ≤ beta) :
-- imply
  quantumIsingSpatialTrotterWeight beta n (L + 1) sigma ≤ Real.exp (beta / (4 * (n : Real))) * quantumIsingOpenSpatialTrotterWeight beta n L sigma := by
-- proof
  apply StatMech.FrontierA.quantumIsingSpatialTrotterWeight_le_exp_mul_open beta n L hn hbeta sigma

/--
[exp_neg_mul_open_le_quantumIsingSpatialTrotterWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma exp_neg_mul_open_le_quantumIsingSpatialTrotterWeight_eq
  {beta : Real}
  {n L : Nat}
  {sigma : QuantumIsingChainConfig (L + 1)}
-- given
  (hn : n ≠ 0)
  (hbeta : 0 ≤ beta) :
-- imply
  Real.exp (-(beta / (4 * (n : Real)))) * quantumIsingOpenSpatialTrotterWeight beta n L sigma ≤ quantumIsingSpatialTrotterWeight beta n (L + 1) sigma := by
-- proof
  apply StatMech.FrontierA.exp_neg_mul_open_le_quantumIsingSpatialTrotterWeight beta n L hn hbeta sigma

/--
[quantumIsingTrotterKernel_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma quantumIsingTrotterKernel_nonneg_eq
  {n : Nat}
  {s t : Bool}
-- given
  (beta h : Real)
  (hbh : 0 ≤ beta * h) :
-- imply
  0 ≤ quantumIsingTrotterKernel beta h n s t := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterKernel_nonneg beta h n hbh s t

/--
[quantumIsingOpenTrotterTransferKernel_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma quantumIsingOpenTrotterTransferKernel_nonneg_eq
  {n L : Nat}
  {sigma tau : QuantumIsingChainConfig (L + 1)}
-- given
  (beta h : Real)
  (hbh : 0 ≤ beta * h) :
-- imply
  0 ≤ quantumIsingOpenTrotterTransferKernel beta h n L sigma tau := by
-- proof
  apply StatMech.FrontierA.quantumIsingOpenTrotterTransferKernel_nonneg beta h n L hbh sigma tau

/--
[quantumIsingOpenTrotterTransferKernel_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma quantumIsingOpenTrotterTransferKernel_add_eq
  {n L M : Nat}
  {sigma tau : QuantumIsingChainConfig (L + M + 2)}
-- given
  (beta h : Real) :
-- imply
  quantumIsingOpenTrotterTransferKernel beta h n (L + M + 1) sigma tau = Real.exp (beta / (4 * (n : Real)) * (quantumIsingSpinSign ((quantumIsingLeftSpatialBlock L M sigma) (Fin.last L)) * quantumIsingSpinSign ((quantumIsingRightSpatialBlock L M sigma) 0))) * quantumIsingOpenTrotterTransferKernel beta h n L (quantumIsingLeftSpatialBlock L M sigma) (quantumIsingLeftSpatialBlock L M tau) * quantumIsingOpenTrotterTransferKernel beta h n M (quantumIsingRightSpatialBlock L M sigma) (quantumIsingRightSpatialBlock L M tau) := by
-- proof
  apply StatMech.FrontierA.quantumIsingOpenTrotterTransferKernel_add beta h n L M sigma tau

/--
[quantumIsingTrotterTransferKernel_le_exp_mul_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma quantumIsingTrotterTransferKernel_le_exp_mul_open_eq
  {n L : Nat}
  {sigma tau : QuantumIsingChainConfig (L + 1)}
-- given
  (beta h : Real)
  (hn : n ≠ 0)
  (hbeta : 0 ≤ beta)
  (hbh : 0 ≤ beta * h) :
-- imply
  quantumIsingTrotterTransferKernel beta h n (L + 1) sigma tau ≤ Real.exp (beta / (4 * (n : Real))) * quantumIsingOpenTrotterTransferKernel beta h n L sigma tau := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterTransferKernel_le_exp_mul_open beta h n L hn hbeta hbh sigma tau

/--
[exp_neg_mul_open_le_quantumIsingTrotterTransferKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma exp_neg_mul_open_le_quantumIsingTrotterTransferKernel_eq
  {n L : Nat}
  {sigma tau : QuantumIsingChainConfig (L + 1)}
-- given
  (beta h : Real)
  (hn : n ≠ 0)
  (hbeta : 0 ≤ beta)
  (hbh : 0 ≤ beta * h) :
-- imply
  Real.exp (-(beta / (4 * (n : Real)))) * quantumIsingOpenTrotterTransferKernel beta h n L sigma tau ≤ quantumIsingTrotterTransferKernel beta h n (L + 1) sigma tau := by
-- proof
  apply StatMech.FrontierA.exp_neg_mul_open_le_quantumIsingTrotterTransferKernel beta h n L hn hbeta hbh sigma tau

/--
[quantumIsingOpenTrotterPathWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma quantumIsingOpenTrotterPathWeight_nonneg_eq
  {n L : Nat}
-- given
  (beta h : Real)
  (hbh : 0 ≤ beta * h)
  (omega : Fin n -> QuantumIsingChainConfig (L + 1)) :
-- imply
  0 ≤ quantumIsingOpenTrotterPathWeight beta h n L omega := by
-- proof
  apply StatMech.FrontierA.quantumIsingOpenTrotterPathWeight_nonneg beta h n L hbh omega

/--
[quantumIsingOpenTrotterPathPartition_add_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma quantumIsingOpenTrotterPathPartition_add_le_eq
  {n L M : Nat}
-- given
  (beta h : Real)
  (hn : n ≠ 0)
  (hbeta : 0 ≤ beta)
  (hbh : 0 ≤ beta * h) :
-- imply
  quantumIsingOpenTrotterPathPartition beta h n (L + M + 1) ≤ Real.exp (beta / 4) * (quantumIsingOpenTrotterPathPartition beta h n L * quantumIsingOpenTrotterPathPartition beta h n M) := by
-- proof
  apply StatMech.FrontierA.quantumIsingOpenTrotterPathPartition_add_le beta h n L M hn hbeta hbh

/--
[quantumIsing_exp_mul_openPartitions_le_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma quantumIsing_exp_mul_openPartitions_le_add_eq
  {n L M : Nat}
-- given
  (beta h : Real)
  (hn : n ≠ 0)
  (hbeta : 0 ≤ beta)
  (hbh : 0 ≤ beta * h) :
-- imply
  Real.exp (-(beta / 4)) * (quantumIsingOpenTrotterPathPartition beta h n L * quantumIsingOpenTrotterPathPartition beta h n M) ≤ quantumIsingOpenTrotterPathPartition beta h n (L + M + 1) := by
-- proof
  apply StatMech.FrontierA.quantumIsing_exp_mul_openPartitions_le_add beta h n L M hn hbeta hbh

/--
[quantumIsingTrotterPathPartition_le_exp_mul_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma quantumIsingTrotterPathPartition_le_exp_mul_open_eq
  {n L : Nat}
-- given
  (beta h : Real)
  (hn : n ≠ 0)
  (hbeta : 0 ≤ beta)
  (hbh : 0 ≤ beta * h) :
-- imply
  quantumIsingTrotterPathPartition beta h n (L + 1) ≤ Real.exp (beta / 4) * quantumIsingOpenTrotterPathPartition beta h n L := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterPathPartition_le_exp_mul_open beta h n L hn hbeta hbh

/--
[exp_neg_mul_open_le_quantumIsingTrotterPathPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma exp_neg_mul_open_le_quantumIsingTrotterPathPartition_eq
  {n L : Nat}
-- given
  (beta h : Real)
  (hn : n ≠ 0)
  (hbeta : 0 ≤ beta)
  (hbh : 0 ≤ beta * h) :
-- imply
  Real.exp (-(beta / 4)) * quantumIsingOpenTrotterPathPartition beta h n L ≤ quantumIsingTrotterPathPartition beta h n (L + 1) := by
-- proof
  apply StatMech.FrontierA.exp_neg_mul_open_le_quantumIsingTrotterPathPartition beta h n L hn hbeta hbh

/--
[quantumIsingTrotterKernel_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma quantumIsingTrotterKernel_pos_eq
  {n : Nat}
  {s t : Bool}
-- given
  (beta h : Real)
  (hn : n ≠ 0)
  (hbh : 0 < beta * h) :
-- imply
  0 < quantumIsingTrotterKernel beta h n s t := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterKernel_pos beta h n hn hbh s t

/--
[quantumIsingOpenTrotterPathWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma quantumIsingOpenTrotterPathWeight_pos_eq
  {n L : Nat}
-- given
  (beta h : Real)
  (hn : n ≠ 0)
  (hbh : 0 < beta * h)
  (omega : Fin n -> QuantumIsingChainConfig (L + 1)) :
-- imply
  0 < quantumIsingOpenTrotterPathWeight beta h n L omega := by
-- proof
  apply StatMech.FrontierA.quantumIsingOpenTrotterPathWeight_pos beta h n L hn hbh omega

/--
[quantumIsingOpenTrotterPathPartition_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma quantumIsingOpenTrotterPathPartition_pos_eq
  {n L : Nat}
-- given
  (beta h : Real)
  (hn : n ≠ 0)
  (hbh : 0 < beta * h) :
-- imply
  0 < quantumIsingOpenTrotterPathPartition beta h n L := by
-- proof
  apply StatMech.FrontierA.quantumIsingOpenTrotterPathPartition_pos beta h n L hn hbh

/--
[quantumIsingOpenTrotterAction_almostAdditive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma quantumIsingOpenTrotterAction_almostAdditive_eq
  {n : Nat}
-- given
  (beta h : Real)
  (hn : n ≠ 0)
  (hbeta : 0 < beta)
  (hbh : 0 < beta * h) :
-- imply
  QuantumIsingAlmostAdditive (quantumIsingOpenTrotterAction beta h n) (1 / 4) := by
-- proof
  apply StatMech.FrontierA.quantumIsingOpenTrotterAction_almostAdditive beta h n hn hbeta hbh

/--
[quantumIsingOpenTrotterFreeEnergy_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma quantumIsingOpenTrotterFreeEnergy_tendsto_eq
  {n : Nat}
-- given
  (beta h : Real)
  (hn : n ≠ 0)
  (hbeta : 0 < beta)
  (hbh : 0 < beta * h) :
-- imply
  Filter.Tendsto (fun L : Nat => quantumIsingOpenTrotterAction beta h n L / L) Filter.atTop (nhds ((quantumIsingOpenTrotterAction_almostAdditive beta h n hn hbeta hbh).limit)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingOpenTrotterFreeEnergy_tendsto beta h n hn hbeta hbh

/--
[quantumIsingOpenTrotterFreeEnergy_uniform_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma quantumIsingOpenTrotterFreeEnergy_uniform_bound_eq
  {n : Nat}
  {L : Nat}
-- given
  (beta h : Real)
  (hn : n ≠ 0)
  (hbeta : 0 < beta)
  (hbh : 0 < beta * h)
  (hL : L ≠ 0) :
-- imply
  |(quantumIsingOpenTrotterAction_almostAdditive beta h n hn hbeta hbh).limit - quantumIsingOpenTrotterAction beta h n L / L| ≤ (1 / 4 : Real) / L := by
-- proof
  apply StatMech.FrontierA.quantumIsingOpenTrotterFreeEnergy_uniform_bound beta h n hn hbeta hbh hL

/--
[quantumIsingTrotterPathPartition_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma quantumIsingTrotterPathPartition_pos_eq
  {n L : Nat}
-- given
  (beta h : Real)
  (hn : n ≠ 0)
  (hbeta : 0 < beta)
  (hbh : 0 < beta * h) :
-- imply
  0 < quantumIsingTrotterPathPartition beta h n (L + 1) := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterPathPartition_pos beta h n L hn hbeta hbh

/--
[abs_quantumIsingPeriodicTrotterAction_sub_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma abs_quantumIsingPeriodicTrotterAction_sub_open_eq
  {n L : Nat}
-- given
  (beta h : Real)
  (hn : n ≠ 0)
  (hbeta : 0 < beta)
  (hbh : 0 < beta * h) :
-- imply
  |quantumIsingPeriodicTrotterAction beta h n L - quantumIsingOpenTrotterAction beta h n L| ≤ 1 / 4 := by
-- proof
  apply StatMech.FrontierA.abs_quantumIsingPeriodicTrotterAction_sub_open beta h n L hn hbeta hbh

/--
[quantumIsingTrotterThermodynamicFreeEnergy_eq_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma quantumIsingTrotterThermodynamicFreeEnergy_eq_limit_eq
  {n : Nat}
-- given
  (beta h : Real)
  (hn : n ≠ 0)
  (hbeta : 0 < beta)
  (hbh : 0 < beta * h) :
-- imply
  quantumIsingTrotterThermodynamicFreeEnergy beta h n = (quantumIsingOpenTrotterAction_almostAdditive beta h n hn hbeta hbh).limit := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterThermodynamicFreeEnergy_eq_limit beta h n hn hbeta hbh

/--
[quantumIsingPeriodicTrotterFreeEnergy_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma quantumIsingPeriodicTrotterFreeEnergy_tendsto_eq
  {n : Nat}
-- given
  (beta h : Real)
  (hn : n ≠ 0)
  (hbeta : 0 < beta)
  (hbh : 0 < beta * h) :
-- imply
  Filter.Tendsto (fun L : Nat => quantumIsingPeriodicTrotterAction beta h n L / L) Filter.atTop (nhds (quantumIsingTrotterThermodynamicFreeEnergy beta h n)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingPeriodicTrotterFreeEnergy_tendsto beta h n hn hbeta hbh

/--
[quantumIsingPeriodicTrotterFreeEnergy_uniform_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean)
-/
@[path]
private lemma quantumIsingPeriodicTrotterFreeEnergy_uniform_bound_eq
  {n : Nat}
  {L : Nat}
-- given
  (beta h : Real)
  (hn : n ≠ 0)
  (hbeta : 0 < beta)
  (hbh : 0 < beta * h)
  (hL : L ≠ 0) :
-- imply
  |quantumIsingTrotterThermodynamicFreeEnergy beta h n - quantumIsingPeriodicTrotterAction beta h n L / L| ≤ 1 / (2 * (L : Real)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingPeriodicTrotterFreeEnergy_uniform_bound beta h n hn hbeta hbh hL


-- created on 2026-10-23
