import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.Z2GaugeInfiniteVolume
open Filter Set Topology StatMech StatMech.FrontierA


/--
[cubicalWilsonExpectation_le_chart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean)
-/
@[path]
private lemma cubicalWilsonExpectation_le_chart_eq
  {a b c A B C : Nat}
  {ox oy oz : Nat}
  {beta : Real}
  {L : Finset (CubicalEdge a b c)}
-- given
  (hx : ox + a ≤ A)
  (hy : oy + b ≤ B)
  (hz : oz + c ≤ C)
  (hbeta : 0 ≤ beta) :
-- imply
  gaugeWilsonExpectation cubicalPlaquetteIncidence (fun _ : CubicalPlaquette a b c => beta) L ≤ gaugeWilsonExpectation cubicalPlaquetteIncidence (fun _ : CubicalPlaquette A B C => beta) (L.map (cubicalEdgeChart ox oy oz hx hy hz)) := by
-- proof
  apply StatMech.FrontierA.cubicalWilsonExpectation_le_chart ox oy oz hx hy hz hbeta L

/--
[cubicalEdgeChart_comp_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean)
-/
@[path]
private lemma cubicalEdgeChart_comp_apply_eq
  {a b c A B C X Y Z : Nat}
  {ox oy oz Ox Oy Oz : Nat}
  {e : CubicalEdge a b c}
-- given
  (hx : ox + a ≤ A)
  (hy : oy + b ≤ B)
  (hz : oz + c ≤ C)
  (hX : Ox + A ≤ X)
  (hY : Oy + B ≤ Y)
  (hZ : Oz + C ≤ Z) :
-- imply
  cubicalEdgeChart Ox Oy Oz hX hY hZ (cubicalEdgeChart ox oy oz hx hy hz e) = cubicalEdgeChart (Ox + ox) (Oy + oy) (Oz + oz) (by omega) (by omega) (by omega) e := by
-- proof
  apply StatMech.FrontierA.cubicalEdgeChart_comp_apply ox oy oz Ox Oy Oz hx hy hz hX hY hZ e

/--
[cubicalPaddedWilsonExpectation_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean)
-/
@[path]
private lemma cubicalPaddedWilsonExpectation_mono_eq
  {beta : Real}
  {a b : Nat}
  {lx rx ly ry lz rz LX RX LY RY LZ RZ : Nat}
-- given
  (hbeta : 0 ≤ beta)
  (hlx : lx ≤ LX)
  (hrx : rx ≤ RX)
  (hly : ly ≤ LY)
  (hry : ry ≤ RY)
  (hlz : lz ≤ LZ)
  (hrz : rz ≤ RZ) :
-- imply
  cubicalPaddedWilsonExpectation beta a b lx rx ly ry lz rz ≤ cubicalPaddedWilsonExpectation beta a b LX RX LY RY LZ RZ := by
-- proof
  apply StatMech.FrontierA.cubicalPaddedWilsonExpectation_mono hbeta a b hlx hrx hly hry hlz hrz

/--
[cubicalFixedLoopWilsonSequence_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean)
-/
@[path]
private lemma cubicalFixedLoopWilsonSequence_mono_eq
  {beta : Real}
  {a b : Nat}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  Monotone (cubicalFixedLoopWilsonSequence beta a b) := by
-- proof
  apply StatMech.FrontierA.cubicalFixedLoopWilsonSequence_mono hbeta a b

/--
[cubicalFixedLoopWilsonSequence_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean)
-/
@[path]
private lemma cubicalFixedLoopWilsonSequence_mem_Icc_eq
  {beta : Real}
  {a b n : Nat}
-- given
  (hbeta : 0 < beta) :
-- imply
  cubicalFixedLoopWilsonSequence beta a b n ∈ Set.Icc 0 1 := by
-- proof
  apply StatMech.FrontierA.cubicalFixedLoopWilsonSequence_mem_Icc hbeta a b n

/--
[cubicalFixedLoopWilsonSequence_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean)
-/
@[path]
private lemma cubicalFixedLoopWilsonSequence_tendsto_eq
  {beta : Real}
  {a b : Nat}
-- given
  (hbeta : 0 < beta) :
-- imply
  Tendsto (cubicalFixedLoopWilsonSequence beta a b) atTop (nhds (cubicalInfiniteVolumeWilsonExpectation beta a b)) := by
-- proof
  apply StatMech.FrontierA.cubicalFixedLoopWilsonSequence_tendsto hbeta a b

/--
[cubicalInfiniteVolumeWilsonExpectation_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean)
-/
@[path]
private lemma cubicalInfiniteVolumeWilsonExpectation_mem_Icc_eq
  {beta : Real}
  {a b : Nat}
-- given
  (hbeta : 0 < beta) :
-- imply
  cubicalInfiniteVolumeWilsonExpectation beta a b ∈ Set.Icc 0 1 := by
-- proof
  apply StatMech.FrontierA.cubicalInfiniteVolumeWilsonExpectation_mem_Icc hbeta a b

/--
[cubicalPaddedWilsonExpectation_le_infiniteVolume](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean)
-/
@[path]
private lemma cubicalPaddedWilsonExpectation_le_infiniteVolume_eq
  {beta : Real}
  {a b lx rx ly ry lz rz : Nat}
-- given
  (hbeta : 0 < beta) :
-- imply
  cubicalPaddedWilsonExpectation beta a b lx rx ly ry lz rz ≤ cubicalInfiniteVolumeWilsonExpectation beta a b := by
-- proof
  apply StatMech.FrontierA.cubicalPaddedWilsonExpectation_le_infiniteVolume hbeta a b lx rx ly ry lz rz

/--
[cubicalPaddedWilsonExpectation_tendsto_infiniteVolume](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean)
-/
@[path]
private lemma cubicalPaddedWilsonExpectation_tendsto_infiniteVolume_eq
  {beta : Real}
  {a b : Nat}
  {lx rx ly ry lz rz : Nat → Nat}
-- given
  (hbeta : 0 < beta)
  (hlx : Tendsto lx atTop atTop)
  (hrx : Tendsto rx atTop atTop)
  (hly : Tendsto ly atTop atTop)
  (hry : Tendsto ry atTop atTop)
  (hlz : Tendsto lz atTop atTop)
  (hrz : Tendsto rz atTop atTop) :
-- imply
  Tendsto (fun n => cubicalPaddedWilsonExpectation beta a b (lx n) (rx n) (ly n) (ry n) (lz n) (rz n)) atTop (nhds (cubicalInfiniteVolumeWilsonExpectation beta a b)) := by
-- proof
  apply StatMech.FrontierA.cubicalPaddedWilsonExpectation_tendsto_infiniteVolume hbeta a b lx rx ly ry lz rz hlx hrx hly hry hlz hrz

/--
[cubicalWilsonExpectation_eq_twistedIsingPartitionRatio_of_surface](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean)
-/
@[path]
private lemma cubicalWilsonExpectation_eq_twistedIsingPartitionRatio_of_surface_eq
  {A B C : Nat}
  {K : CubicalPlaquette A B C → Real}
  {D : Finset (CubicalPlaquette A B C)}
-- given
  (hA : 0 < A)
  (hB : 0 < B)
  (hC : 0 < C)
  (hK : ∀ p, 0 < K p) :
-- imply
  gaugeWilsonExpectation cubicalPlaquetteIncidence K (gaugeSurfaceBoundary cubicalPlaquetteIncidence D) = multibondIsingPartition cubicalDualEnds (multibondTwistCoupling (fun p => gaugeDualCoupling (K p)) D) / multibondIsingPartition cubicalDualEnds (fun p => gaugeDualCoupling (K p)) := by
-- proof
  apply StatMech.FrontierA.cubicalWilsonExpectation_eq_twistedIsingPartitionRatio_of_surface hA hB hC K hK D

/--
[neg_log_cubicalWilsonExpectation_eq_disorderFreeEnergy_of_surface](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean)
-/
@[path]
private lemma neg_log_cubicalWilsonExpectation_eq_disorderFreeEnergy_of_surface_eq
  {A B C : Nat}
  {K : CubicalPlaquette A B C → Real}
  {D : Finset (CubicalPlaquette A B C)}
-- given
  (hA : 0 < A)
  (hB : 0 < B)
  (hC : 0 < C)
  (hK : ∀ p, 0 < K p) :
-- imply
  -Real.log (gaugeWilsonExpectation cubicalPlaquetteIncidence K (gaugeSurfaceBoundary cubicalPlaquetteIncidence D)) = multibondDisorderFreeEnergy cubicalDualEnds (fun p => gaugeDualCoupling (K p)) D := by
-- proof
  apply StatMech.FrontierA.neg_log_cubicalWilsonExpectation_eq_disorderFreeEnergy_of_surface hA hB hC K hK D

/--
[gaugeSurfaceBoundary_cubicalPaddedXYSheet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean)
-/
@[path]
private lemma gaugeSurfaceBoundary_cubicalPaddedXYSheet_eq
  {a b lx rx ly ry lz rz : Nat} :
-- imply
  gaugeSurfaceBoundary cubicalPlaquetteIncidence (cubicalPaddedXYSheet a b lx rx ly ry lz rz) = (cubicalXYLoop (a := a) (b := b) (c := 0) (0 : Fin 1)).map (cubicalEdgeChart lx ly lz (by omega) (by omega) (by omega)) := by
-- proof
  apply StatMech.FrontierA.gaugeSurfaceBoundary_cubicalPaddedXYSheet a b lx rx ly ry lz rz

/--
[cubicalPaddedWilsonExpectation_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean)
-/
@[path]
private lemma cubicalPaddedWilsonExpectation_pos_eq
  {beta : Real}
  {a b lx rx ly ry lz rz : Nat}
-- given
  (hbeta : 0 < beta) :
-- imply
  0 < cubicalPaddedWilsonExpectation beta a b lx rx ly ry lz rz := by
-- proof
  apply StatMech.FrontierA.cubicalPaddedWilsonExpectation_pos hbeta a b lx rx ly ry lz rz

/--
[cubicalInfiniteVolumeWilsonExpectation_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean)
-/
@[path]
private lemma cubicalInfiniteVolumeWilsonExpectation_pos_eq
  {beta : Real}
  {a b : Nat}
-- given
  (hbeta : 0 < beta) :
-- imply
  0 < cubicalInfiniteVolumeWilsonExpectation beta a b := by
-- proof
  apply StatMech.FrontierA.cubicalInfiniteVolumeWilsonExpectation_pos hbeta a b

/--
[neg_log_cubicalPaddedWilsonExpectation_eq_disorderFreeEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean)
-/
@[path]
private lemma neg_log_cubicalPaddedWilsonExpectation_eq_disorderFreeEnergy_eq
  {beta : Real}
  {a b lx rx ly ry lz rz : Nat}
-- given
  (hbeta : 0 < beta)
  (ha : 0 < a)
  (hb : 0 < b)
  (hz : 0 < lz + rz) :
-- imply
  -Real.log (cubicalPaddedWilsonExpectation beta a b lx rx ly ry lz rz) = multibondDisorderFreeEnergy cubicalDualEnds (fun _ : CubicalPlaquette (lx + a + rx) (ly + b + ry) (lz + rz) => gaugeDualCoupling beta) (cubicalPaddedXYSheet a b lx rx ly ry lz rz) := by
-- proof
  apply StatMech.FrontierA.neg_log_cubicalPaddedWilsonExpectation_eq_disorderFreeEnergy hbeta ha hb hz

/--
[cubicalPaddedDisorderFreeEnergy_tendsto_infiniteVolume](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean)
-/
@[path]
private lemma cubicalPaddedDisorderFreeEnergy_tendsto_infiniteVolume_eq
  {beta : Real}
  {a b : Nat}
  {lx rx ly ry lz rz : Nat → Nat}
-- given
  (hbeta : 0 < beta)
  (ha : 0 < a)
  (hb : 0 < b)
  (hlx : Tendsto lx atTop atTop)
  (hrx : Tendsto rx atTop atTop)
  (hly : Tendsto ly atTop atTop)
  (hry : Tendsto ry atTop atTop)
  (hlz : Tendsto lz atTop atTop)
  (hrz : Tendsto rz atTop atTop) :
-- imply
  Tendsto (fun n => cubicalPaddedDisorderFreeEnergy beta a b (lx n) (rx n) (ly n) (ry n) (lz n) (rz n)) atTop (nhds (cubicalInfiniteVolumeWilsonFreeEnergy beta a b)) := by
-- proof
  apply StatMech.FrontierA.cubicalPaddedDisorderFreeEnergy_tendsto_infiniteVolume hbeta ha hb lx rx ly ry lz rz hlx hrx hly hry hlz hrz


-- created on 2026-10-23
