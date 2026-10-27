import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidencePIMSSchedule.Part4
open Filter Topology MeasureTheory StatMech StatMech.FrontierD


/--
[fkRectPIMSDecayDepth_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidencePIMSSchedule.lean)
-/
@[path]
private lemma fkRectPIMSDecayDepth_spec_eq
  {a : Real}
  {p : Nat → Real}
  {k : Nat}
-- given
  (hp_one : ∀ k, p k ≤ 1) :
-- imply
  p k ≤ a ^ fkRectPIMSDecayDepth a p k := by
-- proof
  apply StatMech.FrontierD.fkRectPIMSDecayDepth_spec hp_one k

/--
[tendsto_fkRectPIMSDecayDepth_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidencePIMSSchedule.lean)
-/
@[path]
private lemma tendsto_fkRectPIMSDecayDepth_atTop_eq
  {a : Real}
  {p : Nat → Real}
-- given
  (ha : 0 < a)
  (hp : Tendsto p atTop (nhds 0)) :
-- imply
  Tendsto (fkRectPIMSDecayDepth a p) atTop atTop := by
-- proof
  apply StatMech.FrontierD.tendsto_fkRectPIMSDecayDepth_atTop ha hp

/--
[tendsto_fkRectPIMSSublinearThreshold_div_height_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidencePIMSSchedule.lean)
-/
@[path]
private lemma tendsto_fkRectPIMSSublinearThreshold_div_height_zero_eq
-- given
  (depth height : Nat → Nat)
  (hdepth : Tendsto depth atTop atTop)
  (hheight_pos : ∀ k, 0 < height k) :
-- imply
  Tendsto (fun k => (fkRectPIMSSublinearThreshold (depth k) (height k) : Real) / height k) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_fkRectPIMSSublinearThreshold_div_height_zero depth height hdepth hheight_pos

/--
[fkRect_choose_mul_pow_le_finiteEnergy_of_pimsDepth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidencePIMSSchedule.lean)
-/
@[path]
private lemma fkRect_choose_mul_pow_le_finiteEnergy_of_pimsDepth_eq
  {p c : Real}
-- given
  (hp0 : 0 ≤ p)
  (hc0 : 0 < c)
  (hc1 : c ≤ 1)
  (width height depth : Nat)
  (hdepth : 0 < depth)
  (hpdepth : p ≤ (c / 4) ^ depth)
  (hheight : (c / 2) ^ height ≤ c ^ (2 * width + height) / 2) :
-- imply
  Nat.choose height (height / depth + 1) * p ^ (height / depth + 1) ≤ c ^ (2 * width + height) / 2 := by
-- proof
  apply StatMech.FrontierD.fkRect_choose_mul_pow_le_finiteEnergy_of_pimsDepth hp0 hc0 hc1 width height depth hdepth hpdepth hheight

/--
[exists_fkRectPIMSHeightDominating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidencePIMSSchedule.lean)
-/
@[path]
private lemma exists_fkRectPIMSHeightDominating_eq
  {c : Real}
  {width : Nat} :
-- imply
  ∃ height : Nat, 2 / c ^ (2 * width) ≤ (2 : Real) ^ height := by
-- proof
  apply StatMech.FrontierD.exists_fkRectPIMSHeightDominating c width

/--
[fkRectPIMSHeightLower_width_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidencePIMSSchedule.lean)
-/
@[path]
private lemma fkRectPIMSHeightLower_width_le_eq
  {c : Real}
  {width : Nat} :
-- imply
  width ≤ fkRectPIMSHeightLower c width := by
-- proof
  apply StatMech.FrontierD.fkRectPIMSHeightLower_width_le c width

/--
[fkRectPIMSHeightLower_domination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidencePIMSSchedule.lean)
-/
@[path]
private lemma fkRectPIMSHeightLower_domination_eq
  {c : Real}
-- given
  (hc0 : 0 < c)
  (width height : Nat)
  (hheight : fkRectPIMSHeightLower c width ≤ height) :
-- imply
  (c / 2) ^ height ≤ c ^ (2 * width + height) / 2 := by
-- proof
  apply StatMech.FrontierD.fkRectPIMSHeightLower_domination hc0 width height hheight

/--
[fkRect_pimsDecay_scheduled_binomialSmallness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidencePIMSSchedule.lean)
-/
@[path]
private lemma fkRect_pimsDecay_scheduled_binomialSmallness_eq
  {c : Real}
  {p : Nat → Real}
-- given
  (hc0 : 0 < c)
  (hc1 : c ≤ 1)
  (hp0 : ∀ k, 0 ≤ p k)
  (hp1 : ∀ k, p k ≤ 1)
  (hp : Tendsto p atTop (nhds 0))
  (width height : Nat → Nat)
  (hheight_pos : ∀ k, 0 < height k)
  (hheightLower : ∀ k, fkRectPIMSHeightLower c (width k) ≤ height k) :
-- imply
  let depth := fkRectPIMSDecayDepth (c / 4) p let threshold := fun k => fkRectPIMSSublinearThreshold (depth k) (height k) (∀ k, Nat.choose (height k) (threshold k + 1) * (p k) ^ (threshold k + 1) ≤ c ^ (2 * width k + height k) / 2) ∧ Tendsto (fun k => (threshold k : Real) / height k) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.fkRect_pimsDecay_scheduled_binomialSmallness hc0 hc1 p hp0 hp1 hp width height hheight_pos hheightLower

/--
[fkRect_boxBdryConnEvent_real_tendsto_zero_of_percolation_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidencePIMSSchedule.lean)
-/
@[path]
private lemma fkRect_boxBdryConnEvent_real_tendsto_zero_of_percolation_zero_eq
  {mu : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))}
  [MeasureTheory.IsFiniteMeasure mu]
-- given
  (hperc : mu.real (Percolation.percolationEvent 2) = 0) :
-- imply
  Tendsto (fun n => mu.real (FK.boxBdryConnEvent 2 n)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.fkRect_boxBdryConnEvent_real_tendsto_zero_of_percolation_zero mu hperc

/--
[tendsto_fkRectFixedChargeFreeOneArm_zero_of_percolation_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidencePIMSSchedule.lean)
-/
@[path]
private lemma tendsto_fkRectFixedChargeFreeOneArm_zero_of_percolation_zero_eq
  {q : Real}
  {r : Nat}
-- given
  (hq : 1 ≤ q)
  (hperc : let mu := (FK.freeInfiniteVolume 2 (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq)) (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) (zero_lt_one.trans_le hq) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) mu.real (Percolation.percolationEvent 2) = 0) :
-- imply
  Tendsto (fkRectFixedChargeFreeOneArm hq r) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_fkRectFixedChargeFreeOneArm_zero_of_percolation_zero hq r hperc

/--
[fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_freePIMS_fourCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidencePIMSSchedule.lean)
-/
@[path]
private lemma fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_freePIMS_fourCopy_eq
  {q xiInv : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : 2 ≤ r)
  (hperc : let mu := (FK.freeInfiniteVolume 2 (fkRectCriticalP_pos (by linarith : 0 < q)) (fkRectCriticalP_lt_one (by linarith : 0 < q)) (by linarith : 0 < q) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) mu.real (Percolation.percolationEvent 2) = 0)
  (hwind : ∀ m : Nat → Nat, (∀ k, fkRectBoundaryIncidencePIMSHeightLower q r k ≤ m k) → Tendsto (fun k => -Real.log (fkRectCriticalWindingTailMass (fkRectFixedChargeVerticalFamily r k (m k)) q r) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds (((r - 1 : Nat) : Real) * xiInv)))
  (hfourCopy : ∀ m : Nat → Nat, (∀ k, fkRectBoundaryIncidencePIMSHeightLower q r k ≤ m k) → Tendsto (fun k => fkRectFourCopyShareCost (fkRectFixedChargeVerticalFamily r k (m k)) q / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds 0)) :
-- imply
  ((r - 1 : Nat) : Real) * xiInv ≤ (r : Real) * fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_freePIMS_fourCopy hq r hr hperc hwind hfourCopy


-- created on 2026-10-23
