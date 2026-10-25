import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonFreeEnergy.Part3
open Finset StatMech StatMech.FrontierA


/--
[multibondTwistCoupling_apply_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonFreeEnergy.lean)
-/
@[path]
private lemma multibondTwistCoupling_apply_mem_eq
  [Fintype P]
  [DecidableEq P]
  {J : P → Real}
  {D : Finset P}
  {p : P}
-- given
  (hp : p ∈ D) :
-- imply
  multibondTwistCoupling J D p = -J p := by
-- proof
  apply StatMech.FrontierA.multibondTwistCoupling_apply_mem J D hp

/--
[multibondTwistCoupling_apply_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonFreeEnergy.lean)
-/
@[path]
private lemma multibondTwistCoupling_apply_not_mem_eq
  [Fintype P]
  [DecidableEq P]
  {J : P → Real}
  {D : Finset P}
  {p : P}
-- given
  (hp : p ∉ D) :
-- imply
  multibondTwistCoupling J D p = J p := by
-- proof
  apply StatMech.FrontierA.multibondTwistCoupling_apply_not_mem J D hp

/--
[multibond_twist_energy_eq_shiftedCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonFreeEnergy.lean)
-/
@[path]
private lemma multibond_twist_energy_eq_shiftedCut_eq
  [Fintype P]
  [DecidableEq P]
  {ends : P → V × V}
  {J : P → Real}
  {D : Finset P}
  {s : V → Bool} :
-- imply
  (∑ p : P, multibondTwistCoupling J D p) - 2 * ∑ p ∈ multibondCut ends s, multibondTwistCoupling J D p = (∑ p : P, J p) - 2 * ∑ p ∈ multibondCut ends s ∆ D, J p := by
-- proof
  apply StatMech.FrontierA.multibond_twist_energy_eq_shiftedCut ends J D s

/--
[multibondIsingWeight_twist_eq_shiftedActivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonFreeEnergy.lean)
-/
@[path]
private lemma multibondIsingWeight_twist_eq_shiftedActivity_eq
  [Fintype P]
  [DecidableEq P]
  {ends : P → V × V}
  {J : P → Real}
  {D : Finset P}
  {s : V → Bool} :
-- imply
  multibondIsingWeight ends (multibondTwistCoupling J D) s = Real.exp (∑ p : P, J p) * ∏ p ∈ multibondCut ends s ∆ D, Real.exp (-2 * J p) := by
-- proof
  apply StatMech.FrontierA.multibondIsingWeight_twist_eq_shiftedActivity ends J D s

/--
[multibondIsingPartition_twist_eq_shiftedActivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonFreeEnergy.lean)
-/
@[path]
private lemma multibondIsingPartition_twist_eq_shiftedActivity_eq
  [Fintype P]
  [DecidableEq P]
  {root : V}
  {ends : P → V × V}
  {J : P → Real}
  {D : Finset P} :
-- imply
  multibondIsingPartition ends (multibondTwistCoupling J D) = (2 * Real.exp (∑ p : P, J p)) * ∑ s : AnchoredConfig V root, ∏ p ∈ multibondCut ends s.1 ∆ D, Real.exp (-2 * J p) := by
-- proof
  apply StatMech.FrontierA.multibondIsingPartition_twist_eq_shiftedActivity root ends J D

/--
[multibondIsingPartition_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonFreeEnergy.lean)
-/
@[path]
private lemma multibondIsingPartition_pos_eq
  [Fintype P]
  [DecidableEq P]
  {ends : P → V × V}
  {J : P → Real} :
-- imply
  0 < multibondIsingPartition ends J := by
-- proof
  apply StatMech.FrontierA.multibondIsingPartition_pos ends J

/--
[multibondIsingPartition_eq_Z_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonFreeEnergy.lean)
-/
@[path]
private lemma multibondIsingPartition_eq_Z_neg_one_eq
  [Fintype P]
  [DecidableEq P]
  {ends : P → V × V}
  {J : P → Real} :
-- imply
  multibondIsingPartition ends J = StatMech.Ising.Z (-1) (multibondIsingAction ends J) := by
-- proof
  apply StatMech.FrontierA.multibondIsingPartition_eq_Z_neg_one ends J

/--
[multibondIsingAction_twist_sub_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonFreeEnergy.lean)
-/
@[path]
private lemma multibondIsingAction_twist_sub_abs_le_eq
  [Fintype P]
  [DecidableEq P]
  {ends : P → V × V}
  {J : P → Real}
  {D : Finset P}
  {s : V → Bool} :
-- imply
  |multibondIsingAction ends J s - multibondIsingAction ends (multibondTwistCoupling J D) s| ≤ 2 * ∑ p ∈ D, |J p| := by
-- proof
  apply StatMech.FrontierA.multibondIsingAction_twist_sub_abs_le ends J D s

/--
[multibondDisorderFreeEnergy_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonFreeEnergy.lean)
-/
@[path]
private lemma multibondDisorderFreeEnergy_abs_le_eq
  [Fintype P]
  [DecidableEq P]
  {ends : P → V × V}
  {J : P → Real}
  {D : Finset P} :
-- imply
  |multibondDisorderFreeEnergy ends J D| ≤ 2 * ∑ p ∈ D, |J p| := by
-- proof
  apply StatMech.FrontierA.multibondDisorderFreeEnergy_abs_le ends J D

/--
[multibondIsing_twist_partition_ratio_eq_disorderRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonFreeEnergy.lean)
-/
@[path]
private lemma multibondIsing_twist_partition_ratio_eq_disorderRatio_eq
  [Fintype P]
  [DecidableEq P]
  {root : V}
  {ends : P → V × V}
  {J : P → Real}
  {D : Finset P} :
-- imply
  multibondIsingPartition ends (multibondTwistCoupling J D) / multibondIsingPartition ends J = (∑ s : AnchoredConfig V root, ∏ p ∈ multibondCut ends s.1 ∆ D, Real.exp (-2 * J p)) / (∑ s : AnchoredConfig V root, ∏ p ∈ multibondCut ends s.1, Real.exp (-2 * J p)) := by
-- proof
  apply StatMech.FrontierA.multibondIsing_twist_partition_ratio_eq_disorderRatio root ends J D

/--
[cubicalXYWilsonExpectation_eq_twistedIsingPartitionRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonFreeEnergy.lean)
-/
@[path]
private lemma cubicalXYWilsonExpectation_eq_twistedIsingPartitionRatio_eq
  [Fintype P]
  [DecidableEq P]
  {a b c : Nat}
  {k : Fin (c + 1)}
  {K : CubicalPlaquette a b c → Real}
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (hK : ∀ p, 0 < K p) :
-- imply
  gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) = multibondIsingPartition cubicalDualEnds (multibondTwistCoupling (fun p => gaugeDualCoupling (K p)) (cubicalXYSheet k)) / multibondIsingPartition cubicalDualEnds (fun p => gaugeDualCoupling (K p)) := by
-- proof
  apply StatMech.FrontierA.cubicalXYWilsonExpectation_eq_twistedIsingPartitionRatio ha hb hc k K hK

/--
[neg_log_cubicalXYWilsonExpectation_eq_disorderFreeEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonFreeEnergy.lean)
-/
@[path]
private lemma neg_log_cubicalXYWilsonExpectation_eq_disorderFreeEnergy_eq
  [Fintype P]
  [DecidableEq P]
  {a b c : Nat}
  {k : Fin (c + 1)}
  {K : CubicalPlaquette a b c → Real}
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (hK : ∀ p, 0 < K p) :
-- imply
  -Real.log (gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k)) = multibondDisorderFreeEnergy cubicalDualEnds (fun p => gaugeDualCoupling (K p)) (cubicalXYSheet k) := by
-- proof
  apply StatMech.FrontierA.neg_log_cubicalXYWilsonExpectation_eq_disorderFreeEnergy ha hb hc k K hK

/--
[card_cubicalXYSheet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonFreeEnergy.lean)
-/
@[path]
private lemma card_cubicalXYSheet_eq
  [Fintype P]
  [DecidableEq P]
  {a b c : Nat}
  {k : Fin (c + 1)} :
-- imply
  (cubicalXYSheet (a := a) (b := b) k).card = a * b := by
-- proof
  apply StatMech.FrontierA.card_cubicalXYSheet k

/--
[cubicalXYWilsonFreeEnergy_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonFreeEnergy.lean)
-/
@[path]
private lemma cubicalXYWilsonFreeEnergy_mem_Icc_eq
  [Fintype P]
  [DecidableEq P]
  {a b c : Nat}
  {k : Fin (c + 1)}
  {K : CubicalPlaquette a b c → Real}
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (hK : ∀ p, 0 < K p) :
-- imply
  -Real.log (gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k)) ∈ Set.Icc 0 (2 * ∑ p ∈ cubicalXYSheet k, |gaugeDualCoupling (K p)|) := by
-- proof
  apply StatMech.FrontierA.cubicalXYWilsonFreeEnergy_mem_Icc ha hb hc k K hK

/--
[cubicalXYWilsonFreeEnergy_le_area_mul_dualCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonFreeEnergy.lean)
-/
@[path]
private lemma cubicalXYWilsonFreeEnergy_le_area_mul_dualCoupling_eq
  [Fintype P]
  [DecidableEq P]
  {a b c : Nat}
  {k : Fin (c + 1)}
  {beta : Real}
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (hbeta : 0 < beta) :
-- imply
  -Real.log (gaugeWilsonExpectation cubicalPlaquetteIncidence (fun _ : CubicalPlaquette a b c => beta) (cubicalXYLoop k)) ≤ 2 * (a * b : Nat) * gaugeDualCoupling beta := by
-- proof
  apply StatMech.FrontierA.cubicalXYWilsonFreeEnergy_le_area_mul_dualCoupling ha hb hc k beta hbeta


-- created on 2026-10-23
